import Leanline
import TurboAnki.Store
import TurboAnki.Migrate
import TurboAnki.AnkiImport
import TurboAnki.Core.Shuffle
import TurboAnki.Core.Session

/-!
# The command line

Everything but studying flashcards can also be done without the full-screen interface.
`drill` is melk's terminal drill: the translation is the prompt, you type the word
(line editing by leanline), a typo shows the right spelling in blue, a wrong answer
shows it in red and waits for `Enter`. `Ctrl-D` ends the drill early; the reviews given
so far are already saved.
-/

namespace TurboAnki.Cli

open Leanline

def usage : String := "turbo-anki — spaced repetition with FSRS

Usage:
  turbo-anki                                 the full-screen interface
  turbo-anki decks                           decks with due, new and total counts
  turbo-anki drill <deck> [--new] [--limit N]
                                             typing drill of a dictionary deck
  turbo-anki create-deck <name> [--dictionary]
  turbo-anki import <deck> <file>            add front##back lines to a deck
  turbo-anki import-anki [<collection>]      add Anki's cards as new flashcards (default:
                                             the collection of Anki’s profile “User 1”)
  turbo-anki migrate-melk <dump>             import melk's data: the SQL from
                                             `wrangler d1 export melk --remote --output <dump>`
                                             or a melk SQLite database

Options:
  --db <path>   the database (default: $TURBO_ANKI_DB, else
                ~/.local/share/turbo-anki/turbo-anki.db)"

def blue : String := "\x1b[34m"
def red : String := "\x1b[31m"
def green : String := "\x1b[32m"
def dim : String := "\x1b[2m"
def reset : String := "\x1b[0m"

/-- A deck by name, or by its position in `decks`. -/
def findDeck (store : Store) (name : String) : IO (Deck × DeckStats) := do
  let decks ← store.decks (← Instant.now)
  match decks.find? (·.1.name == name) with
  | some d => return d
  | none =>
    match name.toNat?.bind fun i => decks[i - 1]? with
    | some d => return d
    | none => throw <| IO.userError s!"no deck called {name} (see: turbo-anki decks)"

def listDecks (store : Store) : IO Unit := do
  let decks ← store.decks (← Instant.now)
  if decks.isEmpty then
    IO.println "No decks yet. Create one with: turbo-anki create-deck <name>"
  for ((d, s), i) in decks.zipIdx do
    IO.println s!"{i + 1}. {d.name} [{d.kind.label.toLower}] — due {s.due}/{s.total}, new {s.new}"

/-- The drill loop: asks the current card, grades, saves first answers, repeats. -/
partial def drillLoop (store : Store) (cards : Std.HashMap CardId Card) (d : Drill CardId) :
    InputT IO (Drill CardId) := do
  let some id := d.current? | return d
  let some card := cards[id]? | return d
  let some typed ← getInputLine s!"{dim}{d.pass}/{Drill.passes}{reset} {card.back}> " | do
    outputStrLn ""
    return d
  let g := grade typed card.front
  if d.isFirstAttempt id then
    discard <| liftM (m := IO) <| store.review card (← Instant.now) g.rating
  match g with
  | .typo => outputStrLn s!"{blue}{card.front}{reset}"
  | .wrong =>
    outputStrLn s!"{red}{card.front}{reset}"
    discard <| getInputLine ""
    -- The answer goes away before the next question: up over the empty line and the
    -- red word, clearing both.
    if ← haveTerminalUI then outputStr "\x1b[1A\x1b[2K\x1b[1A\x1b[2K"
  | .correct => pure ()
  drillLoop store cards (d.answer g)

def drill (store : Store) (deckName : String) (mode : Mode) (limit : Option Nat) : IO Unit := do
  let (deck, _) ← findDeck store deckName
  if deck.kind != .dictionary then
    throw <| IO.userError s!"{deck.name} is a flashcard deck; study it in the full-screen interface"
  let limit := min ((limit.getD (sessionLimit deck.kind mode)).max 1) 100
  let cards ← store.sessionCards deck mode (← Instant.now) limit
  if cards.isEmpty then
    IO.println (if mode == .learn then s!"No new cards in {deck.name}." else s!"Nothing due in {deck.name}. 🎉")
    return
  let modeName := if mode == .learn then "new" else "due"
  IO.println s!"{deck.name}: {cards.size} {modeName} card(s), three passes.\n"
  let byId : Std.HashMap CardId Card := cards.foldl (fun m c => m.insert c.id c) {}
  let ids ← shuffleIO (cards.toList.map (·.id))
  -- Answers are not history: recalling the last one with ↑ would give it away.
  let d ← runInputT { autoAddHistory := false } (drillLoop store byId (Drill.start ids))
  let rs := d.firstRatings.map (·.2)
  if rs.isEmpty then
    IO.println "Nothing answered, nothing saved."
  else
    IO.println s!"\n{green}Saved {rs.length} review(s){reset}: {rs.count .good} good, {rs.count .hard} typo, {rs.count .again} missed."

def importFile (store : Store) (deckName : String) (path : System.FilePath) : IO Unit := do
  let (deck, _) ← findDeck store deckName
  let lines := ((← IO.FS.readFile path).splitOn "\n").filter (!·.trimAscii.isEmpty)
  let pairs := (lines.filterMap Pair.parse?).toArray
  for l in lines do
    if (Pair.parse? l).isNone then IO.eprintln s!"skipping malformed line: {l.trimAscii}"
  if pairs.isEmpty then throw <| IO.userError s!"no front##back pairs in {path}"
  let added ← store.importPairs deck.id pairs (← Instant.now)
  IO.println s!"Imported {added}, skipped {pairs.size - added} (of {pairs.size})."

def migrateMelk (store : Store) (path : System.FilePath) : IO Unit := do
  let src ← Migrate.openSource path
  let now ← Instant.now
  let report ← Migrate.run src store now
  IO.println report.summary
  -- Check the result against melk's own counts.
  IO.println "\nDeck                      melk: total  due  new   turbo-anki: total  due  new"
  let ours ← store.decks now
  let mut ok := true
  for (name, total, due, new) in ← Migrate.melkCounts src now do
    let mine := (ours.find? (·.1.name == name)).map (·.2)
    let (t, du, n) := (mine.map fun s => (s.total, s.due, s.new)).getD (0, 0, 0)
    let same := t == total && du == due && n == new
    ok := ok && same
    IO.println s!"{name.pushn ' ' (26 - name.length)}{total}  {due}  {new}   →   {t}  {du}  {n}{if same then "" else "   ≠"}"
  IO.println (if ok then "\nAll counts agree." else "\nSome counts differ (see ≠).")

def importAnki (store : Store) (path : Option System.FilePath) : IO Unit := do
  let path ← match path with
    | some p => pure (if ← p.isDir then p / "collection.anki2" else p)
    | none => AnkiImport.defaultCollection
  let (src, dir) ← AnkiImport.openCopy path
  try
    let report ← AnkiImport.run src store (← Instant.now)
    IO.println s!"From {path}:\n{report.summary}"
  finally
    IO.FS.removeDirAll dir

/-- Command-line arguments: positionals and the values of `--name value` options. -/
structure Args where
  positional : List String := []
  options : List (String × String) := []
  flags : List String := []

def parseArgs (valued : List String) : List String → Args
  | [] => {}
  | a :: rest =>
    if a.startsWith "--" then
      let name := (a.drop 2).toString
      if valued.contains name then
        match rest with
        | v :: rest' => let r := parseArgs valued rest'; { r with options := (name, v) :: r.options }
        | [] => let r := parseArgs valued []; { r with flags := name :: r.flags }
      else let r := parseArgs valued rest; { r with flags := name :: r.flags }
    else let r := parseArgs valued rest; { r with positional := a :: r.positional }

end TurboAnki.Cli
