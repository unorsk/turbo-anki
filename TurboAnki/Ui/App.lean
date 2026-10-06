import TurboAnki.Ui.Views
import TurboAnki.Store
import TurboAnki.Core.Shuffle

/-!
# The application

`run` opens the deck overview and hands the terminal to hyper-vision. Commands from
buttons, menus and the status line arrive at `handle`, which talks to the store and
rebuilds the windows from their state.

Per-window state (a browser's cards, a session) lives in `UiState.views`, keyed by
window id; views of windows that have been closed are dropped on the next command.
Reviews are written to the store as they are given, so a session that is ended early,
or a window that is closed, loses nothing.
-/

namespace TurboAnki.Ui

open HyperVision

/-- What a window shows, beyond its controls. -/
inductive View where
  | browser (deck : Deck) (cards : Array Card)
  | study (v : StudyView)
  | drill (v : DrillView)

structure UiState where
  /-- The rows of the deck overview, in its order. -/
  decks : Array (Deck × DeckStats) := #[]
  views : Array (Nat × View) := #[]

structure Env where
  store : Store
  state : IO.Ref UiState

abbrev M := ReaderT Env IO

namespace App

/-! ## State -/

def getState : M UiState := do (← read).state.get

def modifyState (f : UiState → UiState) : M Unit := do (← read).state.modify f

def view? (id : Nat) : M (Option View) := do
  return ((← getState).views.find? (·.1 == id)).map (·.2)

def setView (id : Nat) (v : View) : M Unit :=
  modifyState fun s => { s with views := (s.views.filter (·.1 != id)).push (id, v) }

def dropView (id : Nat) : M Unit :=
  modifyState fun s => { s with views := s.views.filter (·.1 != id) }

/-- Forgets the views of windows that are gone. -/
def pruneViews (d : Desktop Cmd) : M Unit :=
  modifyState fun s => { s with views := s.views.filter fun (id, _) => (d.find? id).isSome }

/-! ## Desktop helpers -/

def message (d : Desktop Cmd) (title text : String) : Desktop Cmd :=
  d.insertCentered (Window.messageBox title text)

/-- Inserts a window and returns its id. -/
def insert (d : Desktop Cmd) (w : Window Cmd) : Desktop Cmd × Nat := d.insert' w

def deckWindow? (d : Desktop Cmd) : Option (Window Cmd) :=
  d.windows.find? fun w => (w.controlIndex? "decks").isSome

/-- The deck selected in the overview. -/
def selectedDeck? (d : Desktop Cmd) : M (Option (Deck × DeckStats)) := do
  let some w := deckWindow? d | return none
  let some i := (w.control? "decks").bind (·.listFocused?) | return none
  return (← getState).decks[i]?

/-- Reloads the deck overview, keeping the selection on `select` if given. The focus goes
back to the list (a hot key may have left it on a button). -/
def refreshDecks (d : Desktop Cmd) (select : Option DeckId := none) : M (Desktop Cmd) := do
  let now ← Instant.now
  let rows ← (← read).store.decks now
  modifyState fun s => { s with decks := rows }
  let some w := deckWindow? d | return d
  let keep := (w.control? "decks").bind (·.listFocused?) |>.getD 0
  let focus := (select.bind fun id => rows.findIdx? (·.1.id == id)).getD keep
  return d.modify w.id fun _ => { (deckWindow w.bounds rows focus) with
    id := w.id, number := w.number, zoomRect := w.zoomRect }

/-- The text of control `name` of window `w`. -/
def text (w : Window Cmd) (name : String) : String := ((w.control? name).bind (·.text?)).getD ""

/-! ## Card browsers -/

def browserFor? (d : Desktop Cmd) (deck : DeckId) : M (Option Nat) := do
  return (← getState).views.findSome? fun (id, v) => match v with
    | .browser b _ => if b.id == deck && (d.find? id).isSome then some id else none
    | _ => none

/-- Reloads browser `id` from the store, keeping its search and (if given) selecting `card`.
The focus goes to the list, unless `keepFocus` (after a search from the search field). -/
def refreshBrowser (d : Desktop Cmd) (id : Nat) (select : Option CardId := none)
    (keepFocus := false) : M (Desktop Cmd) := do
  let some (.browser deck _) ← view? id | return d
  let some w := d.find? id | return d
  let query := text w "query"
  let cards ← (← read).store.searchCards deck.id query
  setView id (.browser deck cards)
  let keep := (w.control? "cards").bind (·.listFocused?) |>.getD 0
  let focus := (select.bind fun c => cards.findIdx? (·.id == c)).getD keep
  let now ← Instant.now
  let w' := browserWindow w.bounds deck cards query now focus
  return d.modify id fun _ => { w' with
    id := w.id, number := w.number, zoomRect := w.zoomRect,
    focus := if keepFocus then w.focus else w'.focus }

/-- Reloads every browser of `deck`, and the overview. -/
def refreshDeck (d : Desktop Cmd) (deck : DeckId) (select : Option CardId := none) :
    M (Desktop Cmd) := do
  let mut d := d
  for (id, v) in (← getState).views do
    if let .browser b _ := v then
      if b.id == deck then d ← refreshBrowser d id select
  refreshDecks d

/-- The card selected in browser window `w`. -/
def selectedCard? (w : Window Cmd) : M (Option (Deck × Card)) := do
  let some (.browser deck cards) ← view? w.id | return none
  let some i := (w.control? "cards").bind (·.listFocused?) | return none
  return cards[i]?.map (deck, ·)

/-- The browser window a command concerns: the source window, or the active one. -/
def browserWindow? (src : Option (Window Cmd)) (d : Desktop Cmd) : M (Option (Window Cmd)) := do
  for w in src.toList ++ d.top?.toList do
    if let some (.browser ..) ← view? w.id then return some w
  return none

def openBrowser (d : Desktop Cmd) (deck : Deck) : M (Desktop Cmd) := do
  if let some id ← browserFor? d deck.id then return d.raise id
  let cards ← (← read).store.searchCards deck.id ""
  let k : Int := d.windows.size
  let r := centeredRect d.bounds 84 24
  let (d, id) := insert d (browserWindow { r with x := r.x + k, y := r.y + k } deck cards "" (← Instant.now))
  setView id (.browser deck cards)
  return d

/-! ## Sessions -/

def sessionRect (d : Desktop Cmd) : Rect := centeredRect d.bounds 76 20

/-- Rebuilds session window `id` from its view. -/
def redrawSession (d : Desktop Cmd) (id : Nat) : M (Desktop Cmd) := do
  let some w := d.find? id | return d
  let now ← Instant.now
  match ← view? id with
  | some (.study v) => return d.modify id fun _ => { (studyWindow w.bounds v now) with id, number := w.number }
  | some (.drill v) => return d.modify id fun _ => { (drillWindow w.bounds v) with id, number := w.number }
  | _ => return d

def startSession (d : Desktop Cmd) (deck : Deck) (stats : DeckStats) (mode : Mode) :
    M (Desktop Cmd) := do
  let store := (← read).store
  let now ← Instant.now
  let cards ← store.sessionCards deck mode now (sessionLimit deck.kind mode)
  if cards.isEmpty then
    let why := match mode with
      | .review =>
        if stats.new > 0 then s!"^CNothing is due in {deck.name}.\n^CLearn new cards instead?"
        else s!"^CNothing is due in {deck.name}."
      | .learn => s!"^C{deck.name} has no new cards."
    return message d "Nothing to study" why
  let byId : Std.HashMap CardId Card := cards.foldl (fun m c => m.insert c.id c) {}
  -- Due flashcards are shuffled; new flashcards keep the order they were added in.
  -- A drill is always shuffled (melk shuffles once, then repeats the order).
  let ids ← match deck.kind, mode with
    | .flashcards, .learn => pure (cards.toList.map (·.id))
    | _, _ => shuffleIO (cards.toList.map (·.id))
  let view : View := match deck.kind with
    | .flashcards => .study { deck, cards := byId, study := Study.start ids }
    | .dictionary => .drill { deck, cards := byId, drill := Drill.start ids }
  let (d, id) := insert d { title := "", bounds := sessionRect d }
  setView id view
  redrawSession d id

/-- Closes a session window, with a summary of what was studied. -/
def finishSession (d : Desktop Cmd) (id : Nat) : M (Desktop Cmd) := do
  let v ← view? id
  dropView id
  let d ← refreshDecks (d.close id)
  match v with
  | some (.study v) =>
    if v.study.answered == 0 then return d
    return message d "Session over"
      s!"^C{v.deck.name}: {v.study.answered} answer(s)\n^C{tallyText v.tally}"
  | some (.drill v) =>
    let (good, typo, missed) := v.counts
    if v.drill.firstRatings.isEmpty then return d
    let done := if v.drill.isFinished then "Drill complete" else "Drill ended"
    return message d done
      s!"^C{v.deck.name}: saved {v.drill.firstRatings.length} review(s)\n^C{good} good, {typo} typo, {missed} missed"
  | _ => return d

/-- The session window a command concerns. -/
def sessionWindow? (src : Option (Window Cmd)) (d : Desktop Cmd) : M (Option Nat) := do
  for w in src.toList ++ d.top?.toList do
    match ← view? w.id with
    | some (.study _) | some (.drill _) => return some w.id
    | _ => pure ()
  return none

def rate (d : Desktop Cmd) (id : Nat) (r : Rating) : M (Desktop Cmd) := do
  let some (.study v) ← view? id | return d
  let some card := v.current? | return d
  if !v.revealed then return d
  let card ← (← read).store.review card (← Instant.now) r
  let graduated := match card.sched with
    | .seen s => s.phase == .review
    | .new => true
  let v := { v with cards := v.cards.insert card.id card, study := v.study.answer graduated,
                    revealed := false, tally := v.tally.modify (r.toNat - 1) (· + 1) }
  setView id (.study v)
  if v.study.isFinished then finishSession d id else redrawSession d id

def check (d : Desktop Cmd) (id : Nat) : M (Desktop Cmd) := do
  let some (.drill v) ← view? id | return d
  if v.waiting then
    -- The next question appears on a clean slate.
    setView id (.drill { v with waiting := false, feedback := none })
    return ← redrawSession d id
  let some card := v.current? | return d
  let some w := d.find? id | return d
  let typed := text w "answer"
  let g := grade typed card.front
  -- The first answer to a card is its review; later passes are practice.
  let v ← if v.drill.isFirstAttempt card.id then do
      let card ← (← read).store.review card (← Instant.now) g.rating
      pure { v with cards := v.cards.insert card.id card }
    else pure v
  -- A correct answer needs no comment; a typo shows the spelling under the next
  -- question; a wrong answer shows the word until Enter.
  let feedback := if g == .correct then none
    else some { grade := g, prompt := card.back, expected := card.front, typed }
  let v := { v with drill := v.drill.answer g, waiting := g == .wrong, feedback }
  setView id (.drill v)
  if v.drill.isFinished then finishSession d id else redrawSession d id

/-! ## Decks -/

def withDeck (d : Desktop Cmd) (f : Deck × DeckStats → M (Desktop Cmd)) : M (Desktop Cmd) := do
  match ← selectedDeck? d with
  | some ds => f ds
  | none => return message d "No deck" "^CCreate a deck first (New deck…)."

def deckKindOf (w : Window Cmd) : DeckKind :=
  if ((w.control? "kind").bind (·.selected?)) == some 1 then .dictionary else .flashcards

/-- Replaces dialog `w` by the same dialog showing an error. -/
def redoDialog (d : Desktop Cmd) (w : Window Cmd) (w' : Window Cmd) : Desktop Cmd :=
  d.modify w.id fun _ => { w' with id := w.id, bounds := w.bounds }

/-- Opens the editor for the card selected in the browser. -/
def editSelected (src : Option (Window Cmd)) (d : Desktop Cmd) : M (Desktop Cmd) := do
  let some w ← browserWindow? src d | return d
  let some (deck, card) ← selectedCard? w | return d
  return d.insert (cardDialog d.bounds deck "Edit card" card.front card.back (.saveCard card.id))

/-! ## Commands -/

def handle (cmd : Cmd) (src : Option (Window Cmd)) (d : Desktop Cmd) : M (Desktop Cmd) := do
  pruneViews d
  let store := (← read).store
  match cmd with
  | .showDecks =>
    let d ← refreshDecks d
    return match deckWindow? d with
      | some w => d.raise w.id
      | none => d
  | .study => withDeck d fun (deck, s) => startSession d deck s (if s.due > 0 then .review else .learn)
  | .review => withDeck d fun (deck, s) => startSession d deck s .review
  | .learn => withDeck d fun (deck, s) => startSession d deck s .learn
  | .browse => withDeck d fun (deck, _) => openBrowser d deck
  | .newDeck => return d.insert (deckNameDialog d.bounds "New deck" "" true .createDeck)
  | .createDeck =>
    let some w := src | return d
    match ← store.createDeck (text w "name") (deckKindOf w) (← Instant.now) with
    | .ok id => refreshDecks (d.close w.id) (select := some id)
    | .error e =>
      -- The same dialog with the error, keeping the kind that was chosen.
      let w' := deckNameDialog d.bounds "New deck" (text w "name") true .createDeck e.message
      let kind := w.control? "kind"
      return redoDialog d w { w' with controls := w'.controls.map fun c =>
        if c.name == "kind" then kind.getD c else c }
  | .renameDeck => withDeck d fun (deck, _) =>
    return d.insert (deckNameDialog d.bounds s!"Rename {deck.name}" deck.name false (.saveDeckName deck.id))
  | .saveDeckName id =>
    let some w := src | return d
    match ← store.renameDeck id (text w "name") with
    | .ok () =>
      let d ← refreshDecks (d.close w.id) (select := some id)
      -- Browsers and sessions show the name in their titles.
      let decks := (← getState).decks
      let some (deck, _) := decks.find? (·.1.id == id) | return d
      let mut d := d
      for (wid, v) in (← getState).views do
        match v with
        | .browser b cs => if b.id == id then setView wid (.browser deck cs); d ← refreshBrowser d wid
        | .study sv => if sv.deck.id == id then setView wid (.study { sv with deck }); d ← redrawSession d wid
        | .drill dv => if dv.deck.id == id then setView wid (.drill { dv with deck }); d ← redrawSession d wid
      return d
    | .error e =>
      return redoDialog d w (deckNameDialog d.bounds w.title (text w "name") false (.saveDeckName id) e.message)
  | .deleteDeck => withDeck d fun (deck, s) =>
    return d.insert (confirmDialog d.bounds "Delete deck"
      s!"Delete “{deck.name}” and its {s.total} card(s),\nwith all their review history?" "~D~elete"
      (.confirmDeleteDeck deck.id))
  | .confirmDeleteDeck id =>
    store.deleteDeck id
    let mut d := d
    for (wid, v) in (← getState).views do
      let gone := match v with
        | .browser b _ => b.id == id
        | .study sv => sv.deck.id == id
        | .drill dv => dv.deck.id == id
      if gone then d := d.close wid; dropView wid
    refreshDecks (match src with | some w => d.close w.id | none => d)
  | .importWords => withDeck d fun (deck, _) =>
    return d.insertCentered (← Window.fileDialog s!"Import words into {deck.name}" (.importFile deck.id))
  | .importFile id =>
    let some path := src.bind FileDialog.path? | return d
    let content ← IO.FS.readFile path
    let lines := (content.splitOn "\n").filter (!·.trimAscii.isEmpty)
    let pairs := (lines.filterMap Pair.parse?).toArray
    let added ← store.importPairs id pairs (← Instant.now)
    let d ← refreshDeck d id
    let bad := lines.length - pairs.size
    return message d "Import"
      (s!"^CAdded {added} card(s); {pairs.size - added} were already in the deck." ++
        (if bad > 0 then s!"\n^C{bad} line(s) were not “front##back” pairs." else ""))
  | .browserEnter =>
    let some w ← browserWindow? src d | return d
    if (w.focused?.map (·.name)) == some "query" then refreshBrowser d w.id (keepFocus := true)
    else editSelected (some w) d
  | .addCard =>
    let some w ← browserWindow? src d | return d
    let some (.browser deck _) ← view? w.id | return d
    return d.insert (cardDialog d.bounds deck s!"Add to {deck.name}" "" "" (.saveNewCard deck.id))
  | .saveNewCard id =>
    let some w := src | return d
    let decks := (← getState).decks
    let some (deck, _) := decks.find? (·.1.id == id) | return d.close w.id
    let (front, back) := (text w "front", text w "back")
    match ← store.addCard id front back (← Instant.now) with
    | .ok cid =>
      -- The dialog stays open for the next card.
      let d := redoDialog d w (cardDialog d.bounds deck w.title "" "" (.saveNewCard id)
        s!"Added “{firstLine front.trimAscii.toString}”. Next card, or Cancel." okAttr)
      refreshDeck d id (select := some cid)
    | .error e => return redoDialog d w (cardDialog d.bounds deck w.title front back (.saveNewCard id) e.message)
  | .editCard => editSelected src d
  | .saveCard id =>
    let some w := src | return d
    let some card ← store.card? id | return d.close w.id
    let (front, back) := (text w "front", text w "back")
    match ← store.updateCard id front back with
    | .ok () => refreshDeck (d.close w.id) card.deckId (select := some id)
    | .error e =>
      let decks := (← getState).decks
      let some (deck, _) := decks.find? (·.1.id == card.deckId) | return d.close w.id
      return redoDialog d w (cardDialog d.bounds deck "Edit card" front back (.saveCard id) e.message)
  | .deleteCard =>
    let some w ← browserWindow? src d | return d
    let some (_, card) ← selectedCard? w | return d
    return d.insert (confirmDialog d.bounds "Delete card"
      s!"Delete “{firstLine card.front}” and its review history?" "~D~elete" (.confirmDeleteCard card.id))
  | .confirmDeleteCard id =>
    let some card ← store.card? id | return d
    store.deleteCard id
    refreshDeck (match src with | some w => d.close w.id | none => d) card.deckId
  | .resetCard =>
    let some w ← browserWindow? src d | return d
    let some (_, card) ← selectedCard? w | return d
    return d.insert (confirmDialog d.bounds "Reset card"
      s!"Make “{firstLine card.front}” new again?\nIts schedule is forgotten; its history is kept." "~R~eset"
      (.confirmResetCard card.id))
  | .confirmResetCard id =>
    let some card ← store.card? id | return d
    store.resetCard id
    refreshDeck (match src with | some w => d.close w.id | none => d) card.deckId (select := some id)
  | .reveal =>
    let some id ← sessionWindow? src d | return d
    let some (.study v) ← view? id | return d
    setView id (.study { v with revealed := true })
    redrawSession d id
  | .rate r =>
    let some id ← sessionWindow? src d | return d
    rate d id r
  | .check =>
    let some id ← sessionWindow? src d | return d
    check d id
  | .endSession =>
    let some id ← sessionWindow? src d | return d
    finishSession d id
  | .about =>
    return message d "About"
      "^Cturbo-anki\n^Cspaced repetition with FSRS-5\n\n^CFlashcards: show the answer, rate 1–4.\n^CDictionaries: type the word, three passes."

/-! ## Running -/

def menuBar : Array (Menu Cmd) := #[
  Menu.new "~≡~" #[
    MenuItem.item "~A~bout…" (.user .about),
    .separator,
    MenuItem.item "E~x~it" .quit (some (KeyEvent.alt 'x'))],
  Menu.new "~D~ecks" #[
    MenuItem.item "~S~tudy" (.user .study),
    MenuItem.item "~R~eview due" (.user .review),
    MenuItem.item "~L~earn new" (.user .learn),
    MenuItem.item "~C~ards…" (.user .browse),
    .separator,
    MenuItem.item "~N~ew deck…" (.user .newDeck),
    MenuItem.item "Rena~m~e…" (.user .renameDeck),
    MenuItem.item "~D~elete…" (.user .deleteDeck),
    MenuItem.item "~I~mport words…" (.user .importWords),
    .separator,
    MenuItem.item "Deck ~o~verview" (.user .showDecks) (some (KeyEvent.plain (.f 2)))],
  Menu.new "~W~indow" #[
    MenuItem.item "~Z~oom" .zoom (some (KeyEvent.plain (.f 5))),
    MenuItem.item "~N~ext" .nextWindow (some (KeyEvent.plain (.f 6))),
    MenuItem.item "~P~revious" .prevWindow (some ⟨.f 6, { shift := true }⟩),
    MenuItem.item "~C~lose" .close (some ⟨.f 3, { alt := true }⟩)]]

def statusLine : Array (StatusItem Cmd) := #[
  StatusItem.new "~Alt-X~ Exit" (KeyEvent.alt 'x') .quit,
  StatusItem.new "~F2~ Decks" (KeyEvent.plain (.f 2)) (.user .showDecks),
  StatusItem.new "~F5~ Zoom" (KeyEvent.plain (.f 5)) .zoom,
  StatusItem.new "~F6~ Next" (KeyEvent.plain (.f 6)) .nextWindow,
  StatusItem.new "~F10~ Menu" (KeyEvent.plain (.f 10)) .menu]

def newEnv (store : Store) : IO Env := do
  let rows ← store.decks (← Instant.now)
  return { store, state := ← IO.mkRef { decks := rows } }

/-- The application, on `env`. A failing command shows its error instead of ending the
program. -/
def make (env : Env) : HyperVision.App Cmd :=
  let onCommand (cmd : Cmd) (src : Option (Window Cmd)) (d : Desktop Cmd) : IO (Handled Cmd) := do
    try
      return ((← (handle cmd src d).run env) : Desktop Cmd)
    catch e =>
      return message d "Error" (toString e)
  { menuBar, statusLine, onCommand }

/-- The deck overview, sized for a desktop. -/
def initialWindow (env : Env) (desk : Rect) : IO (Window Cmd) := do
  return deckWindow (centeredRect desk 80 22) (← env.state.get).decks

/-- Runs the user interface on the store. -/
def run (store : Store) : IO Unit := do
  let env ← newEnv store
  let (w, h) ← Terminal.size
  (make env).run #[← initialWindow env ⟨0, 1, w, h - 2⟩]

end App

end TurboAnki.Ui
