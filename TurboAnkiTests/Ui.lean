import TurboAnki

/-!
# The user interface, driven headlessly

The real application (`TurboAnki.Ui.App.make`) on a scratch database, fed key presses
through hyper-vision's event handling and rendered to text — no terminal needed. Each
scenario plays a session the way a person would and then checks the store.
-/

namespace TurboAnkiTests.Ui

open HyperVision TurboAnki TurboAnki.Ui

structure Driver where
  env : Env
  app : HyperVision.App Cmd
  st : IO.Ref (AppState Cmd)
  verbose : Bool

def Driver.new (store : Store) (verbose : Bool) (w : Nat := 100) (h : Nat := 30) : IO Driver := do
  let env ← TurboAnki.Ui.App.newEnv store
  let desk := HyperVision.App.desktopRect ⟨w, h⟩
  let win ← TurboAnki.Ui.App.initialWindow env desk
  let desktop := ({ bounds := desk } : Desktop Cmd).insert win
  return { env, app := TurboAnki.Ui.App.make env, st := ← IO.mkRef { desktop, screen := ⟨w, h⟩ }, verbose }

def Driver.event (dr : Driver) (ev : Event) : IO Unit := do
  let (_, st) ← ((HyperVision.App.handleEvent ev).run dr.app).run (← dr.st.get)
  dr.st.set st

def Driver.key (dr : Driver) (k : KeyEvent) : IO Unit := dr.event (.key k)
def Driver.press (dr : Driver) (k : Key) : IO Unit := dr.key (KeyEvent.plain k)
def Driver.char (dr : Driver) (c : Char) : IO Unit := dr.key (KeyEvent.plain (.char c))
def Driver.alt (dr : Driver) (c : Char) : IO Unit := dr.key (KeyEvent.alt c)
def Driver.type (dr : Driver) (s : String) : IO Unit := s.toList.forM dr.char

def Driver.screen (dr : Driver) : IO String := do
  let st ← dr.st.get
  let ((scr, _), _) ← (HyperVision.App.render.run dr.app).run st
  let rows := (List.range scr.height).map fun (y : Nat) =>
    String.ofList ((List.range scr.width).map fun (x : Nat) =>
      ((scr.get? (x : Int) (y : Int)).map (·.ch)).getD ' ')
  return "\n".intercalate (rows.map (·.trimAsciiEnd.toString))

def Driver.show (dr : Driver) (caption : String) : IO Unit := do
  if dr.verbose then IO.println s!"── {caption} ──\n{← dr.screen}\n"

def Driver.sees (dr : Driver) (text : String) : IO Bool := do
  return ((← dr.screen).splitOn text).length > 1

def expect (ok : Bool) (msg : String) : IO Unit :=
  unless ok do throw <| IO.userError s!"UI test failed: {msg}"

def Driver.expectSees (dr : Driver) (text : String) : IO Unit := do
  unless ← dr.sees text do
    IO.println (← dr.screen)
    throw <| IO.userError s!"UI test failed: expected to see “{text}”"

/-- The drill view of the front window. -/
def Driver.drill? (dr : Driver) : IO (Option DrillView) := do
  let st ← dr.st.get
  let some w := st.desktop.top? | return none
  let ui ← dr.env.state.get
  return ui.views.findSome? fun (id, v) => match v with
    | .drill d => if id == w.id then some d else none
    | _ => none

def reviewCount (store : Store) : IO Nat := do
  let stmt ← store.db.prepare "SELECT COUNT(*) FROM reviews"
  discard stmt.step
  return (← stmt.columnInt64 0).toInt.toNat

def deckStats (store : Store) (name : String) : IO (Option (Deck × DeckStats)) := do
  return (← store.decks (← Instant.now)).find? (·.1.name == name)

/-- Studying flashcards: reveal, rate, see learning cards come back, finish. -/
def flashcards (dr : Driver) (store : Store) : IO Unit := do
  dr.show "deck overview"
  dr.expectSees "capitals"
  dr.press .enter -- Study: nothing is due, so new cards
  dr.expectSees "Study: capitals"
  dr.expectSees "Norway"
  dr.show "a flashcard"
  expect (!(← dr.sees "Oslo")) "the answer shows before it is revealed"
  dr.char ' ' -- the focused Show answer button
  dr.expectSees "Oslo"
  dr.expectSees "Good 10m" -- a new card rated Good comes back in ten minutes
  dr.show "revealed, with the interval each rating gives"
  dr.char '3' -- Good: still learning, back at the end of the queue
  dr.expectSees "Sweden"
  dr.press .enter
  dr.char '4' -- Easy: graduates, leaves the session
  dr.expectSees "France"
  dr.press .enter
  dr.char '1' -- Again
  dr.expectSees "Norway" -- back again
  dr.press .enter
  dr.char '3'
  dr.expectSees "France"
  dr.press .enter
  dr.char '3'
  dr.expectSees "Session over"
  dr.show "end of the session"
  dr.press .enter
  expect ((← reviewCount store) == 5) "five reviews were not recorded"
  let some (_, s) ← deckStats store "capitals" | expect false "deck missing"
  expect (s.new == 0 && s.due == 0) s!"after studying, capitals is {repr s}"

/-- A typing drill: correct, wrong (and continue), until all three passes are done. -/
def drill (dr : Driver) (store : Store) : IO Unit := do
  let before ← reviewCount store
  dr.press .down -- norsk
  dr.char 's'
  dr.expectSees "Drill: norsk"
  dr.expectSees "Pass 1 of 3"
  dr.show "a drill prompt"
  let some v ← dr.drill? | expect false "no drill view"
  let some first := v.current? | expect false "no current card"
  dr.type first.front
  dr.press .enter
  -- A correct answer is not commented on: the next question just appears.
  expect (!(← dr.sees s!"✓ {first.front}")) "a correct answer was commented on"
  let some v ← dr.drill? | expect false "no drill view"
  let some second := v.current? | expect false "no current card"
  dr.type "xyzzy"
  dr.press .enter
  dr.expectSees "Press Enter to continue"
  dr.show "after a wrong answer"
  dr.press .enter
  -- With the next question showing, the wrong answer is gone.
  expect (!(← dr.sees "Press Enter to continue")) "the wrong answer stayed after Enter"
  expect (!(← dr.sees s!"→ {second.front}")) "the wrong answer stayed after Enter"
  -- A typo with the accent left out is accepted, shown with the right spelling.
  let mut steps := 0
  repeat
    let some v ← dr.drill? | break
    let some card := v.current? | break
    let answer := if card.front == "får" then "far" else card.front
    dr.type answer
    dr.press .enter
    steps := steps + 1
    if steps > 20 then break
  expect (steps == 5) s!"the drill took {steps} more answers instead of 5"
  dr.expectSees "Drill complete"
  dr.show "end of the drill"
  dr.press .enter
  expect ((← reviewCount store) == before + 2) "a drill must review each card exactly once"
  let stmt ← store.db.prepare s!"SELECT rating FROM reviews r JOIN cards c ON c.id = r.card_id
    WHERE c.front = '{second.front}' ORDER BY r.id DESC LIMIT 1"
  discard stmt.step
  expect ((← stmt.columnInt64 0) == 1) "the wrong first answer was not rated Again"

/-- Adding, editing and deleting cards in the card browser. -/
def editing (dr : Driver) (store : Store) : IO Unit := do
  dr.press .up -- capitals
  dr.char 'c'
  dr.expectSees "Cards: capitals"
  dr.char 'a'
  dr.expectSees "Add to capitals"
  dr.type "Italy"
  dr.press .tab
  dr.type "Rome"
  dr.alt 's'
  dr.expectSees "Added “Italy”"
  dr.show "adding cards"
  dr.press .escape
  dr.expectSees "Italy"
  dr.show "the browser"
  let some (deck, s) ← deckStats store "capitals" | expect false "deck missing"
  expect (s.total == 4) "the card was not added"
  -- Italy is selected after adding it.
  dr.press .enter
  dr.expectSees "Edit card"
  dr.press .tab
  dr.press .end
  dr.type " (Roma)"
  dr.alt 's'
  let cards ← store.searchCards deck.id "Italy"
  expect ((cards.map (·.back)) == #["Rome (Roma)"]) s!"the edit was not saved: {repr (cards.map (·.back))}"
  -- A duplicate front is refused, in the dialog.
  dr.char 'a'
  dr.type "France"
  dr.press .tab
  dr.type "Paris"
  dr.alt 's'
  dr.expectSees "already has a card “France”"
  dr.press .escape
  -- Searching filters the list.
  dr.alt 'f'
  dr.type "swe"
  dr.press .enter
  dr.expectSees "1 card(s)"
  dr.show "a search"
  dr.alt 'f'
  dr.key ⟨.char 'y', { ctrl := true }⟩
  dr.press .enter
  dr.expectSees "4 card(s)"
  -- Deleting asks first; Enter there means Cancel.
  dr.press .tab
  dr.press .tab
  dr.char 'd'
  dr.expectSees "Delete card"
  dr.press .enter
  expect ((← store.searchCards deck.id "").size == 4) "Enter in the confirmation deleted the card"
  dr.char 'd'
  dr.char 'd'
  expect ((← store.searchCards deck.id "").size == 3) "the card was not deleted"
  dr.key ⟨.f 3, { alt := true }⟩ -- close the browser

/-- Creating, renaming and deleting decks. -/
def decks (dr : Driver) (store : Store) : IO Unit := do
  dr.char 'n'
  dr.expectSees "New deck"
  dr.type "norsk"
  dr.press .enter
  dr.expectSees "There is already a deck called “norsk”."
  dr.key ⟨.char 'y', { ctrl := true }⟩
  dr.type "spanish"
  dr.press .tab
  dr.press .down -- Dictionary
  dr.press .enter
  let some (d, _) ← deckStats store "spanish" | expect false "the deck was not created"
  expect (d.kind == .dictionary) "the deck has the wrong kind"
  dr.show "a new deck"
  dr.char 'm'
  dr.type "español"
  dr.press .enter
  expect (← deckStats store "español").isSome "the deck was not renamed"
  dr.char 'd'
  dr.char 'd'
  expect (← deckStats store "español").isNone "the deck was not deleted"
  dr.show "after deleting it"

def run (verbose : Bool) (path : System.FilePath) : IO Unit := do
  let store ← Store.openAt path
  let now ← Instant.now
  let .ok caps ← store.createDeck "capitals" .flashcards now | throw (IO.userError "createDeck")
  let .ok norsk ← store.createDeck "norsk" .dictionary now | throw (IO.userError "createDeck")
  for (f, b) in [("Norway", "Oslo"), ("Sweden", "Stockholm"), ("France", "Paris")] do
    discard <| store.addCard caps f b now
  for (f, b) in [("hund", "dog"), ("får", "sheep")] do
    discard <| store.addCard norsk f b now
  let dr ← Driver.new store verbose
  flashcards dr store
  drill dr store
  editing dr store
  decks dr store
  IO.println "UI scenarios: flashcards, drill, card editing, decks — all passed"

end TurboAnkiTests.Ui
