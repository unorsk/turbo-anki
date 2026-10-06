import TurboAnki.Store
import TurboAnki.Core.Html

/-!
# Importing an Anki collection

Reads an Anki collection (`collection.anki2`, schema 11 to 18) and adds its cards to
flashcard decks of the same names, as new cards: the Anki history is not kept.

* Anki nests decks with a separator; `Default::Cybersecurity` keeps the nesting in the
  name.
* A card's front and back are its note's first two fields, swapped for the second card
  of a reversed note type (template 1). Cards of other templates, and cloze notes, have
  no front/back reading, so they are reported and skipped.
* Fields are HTML; `Html.toText` flattens them.
* The collection is copied before it is opened (read-only), so Anki's file is never
  touched, even if Anki is running.
* Running it again adds only what is missing (cards are matched by front).

Anki's own tables use a collation (`unicase`) that SQLite does not know; the queries here
avoid the columns and indexes that need it.
-/

namespace TurboAnki.AnkiImport

open SQLite

structure AnkiCard where
  deckId : Int64
  ord : Int64
  fields : String
deriving SQLite.Row

/-- What an import did. -/
structure Report where
  decksCreated : Array String := #[]
  decksReused : Array String := #[]
  added : Nat := 0
  alreadyThere : Nat := 0
  skipped : Array String := #[]

def Report.summary (r : Report) : String :=
  s!"{r.decksCreated.size} deck(s) created, {r.decksReused.size} already there; " ++
  s!"{r.added} card(s) added, {r.alreadyThere} already there" ++
  (if r.skipped.isEmpty then "." else s!"; {r.skipped.size} skipped:\n  " ++
    "\n  ".intercalate r.skipped.toList)

/-- Anki's separator of nested deck names (`\x1f` since schema 18, `::` before). -/
def deckName (raw : String) : String := "::".intercalate (raw.splitOn "\x1f")

/-- Whether a field has cloze deletions (`{{c1::…}}`). -/
def hasCloze (s : String) : Bool :=
  (s.splitOn "{{c").drop 1 |>.any fun tail =>
    let digits := tail.toList.takeWhile Char.isDigit
    !digits.isEmpty && (tail.toList.drop digits.length).take 2 == [':', ':']

/-- A card's front and back, from its note's fields (separated by `\x1f`) and its template. -/
def frontBack (fields : String) (ord : Nat) : Except String Pair := do
  let fs := (fields.splitOn "\x1f").map Html.toText
  if hasCloze fields then .error "a cloze note"
  let (front, back) ← match fs, ord with
    | f :: b :: _, 0 => pure (f, b)
    | f :: b :: _, 1 => pure (b, f)
    | [_], _ => .error "a note with a single field"
    | _, _ => .error s!"card {ord + 1} of a note type with more than two cards"
  if front.isEmpty then .error "the front is empty"
  if back.isEmpty then .error "the back is empty"
  return { front, back }

/-- Opens a copy of the collection at `path` (with its write-ahead log, if any). -/
def openCopy (path : System.FilePath) : IO (SQLite × System.FilePath) := do
  unless ← path.pathExists do throw <| IO.userError s!"no Anki collection at {path}"
  let dir ← IO.FS.createTempDir
  let copy := dir / "collection.anki2"
  IO.FS.writeBinFile copy (← IO.FS.readBinFile path)
  let wal : System.FilePath := path.toString ++ "-wal"
  if ← wal.pathExists then
    IO.FS.writeBinFile (copy.toString ++ "-wal") (← IO.FS.readBinFile wal)
  return (← SQLite.openWith copy .readWrite, dir)

/-- Adds the cards of the Anki collection `src` to `store`. -/
def run (src : SQLite) (store : Store) (now : Instant) : IO Report := do
  let decks : Array (Int64 × String) ← (← src.prepare "SELECT id, name FROM decks").results.toArray
  let cards : Array AnkiCard ← (← src.prepare "SELECT c.did, c.ord, n.flds
      FROM cards c JOIN notes n ON n.id = c.nid ORDER BY c.did, n.id, c.ord").results.toArray
  let mut report : Report := {}
  for (did, raw) in decks do
    let name := deckName raw
    let mut pairs : Array Pair := #[]
    for c in cards.filter (·.deckId == did) do
      match frontBack c.fields c.ord.toInt.toNat with
      | .ok p =>
        if pairs.any (·.front == p.front) then
          report := { report with skipped := (report.skipped.push
            s!"{name}: “{p.front}”: a second card with the same front") }
        else pairs := pairs.push p
      | .error why =>
        let shown := Html.toText ((c.fields.splitOn "\x1f").headD "")
        report := { report with skipped := report.skipped.push s!"{name}: “{shown}”: {why}" }
    -- Decks without cards (Anki's parents of nested decks, empty decks) are not created.
    if pairs.isEmpty then continue
    let deck ← match ← store.deckNamed? name with
      | some d =>
        report := { report with decksReused := report.decksReused.push name }
        pure d.id
      | none =>
        match ← store.createDeck name .flashcards now with
        | .ok id =>
          report := { report with decksCreated := report.decksCreated.push name }
          pure id
        | .error e => throw <| IO.userError e.message
    let added ← store.importPairs deck pairs now
    report := { report with added := report.added + added,
                            alreadyThere := report.alreadyThere + (pairs.size - added) }
  return report

/-- Anki's default profile on this system. -/
def defaultCollection : IO System.FilePath := do
  let some home ← IO.getEnv "HOME" | throw <| IO.userError "cannot find the home directory"
  let base : System.FilePath :=
    if System.Platform.isOSX then System.FilePath.mk home / "Library" / "Application Support" / "Anki2"
    else System.FilePath.mk home / ".local" / "share" / "Anki2"
  return base / "User 1" / "collection.anki2"

end TurboAnki.AnkiImport
