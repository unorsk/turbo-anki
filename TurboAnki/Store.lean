import SQLite
import TurboAnki.Core.Model

/-!
# The store

All data lives in one SQLite database. The schema mirrors the types: a card in state
`0` (new) has no due date and no last review, every other card has both, ratings are
`1‥4` — the database refuses rows that the `Sched` type could not represent, and
`Card.ofRow` refuses them again on the way in.

Times are stored as milliseconds since the Unix epoch.
-/

namespace TurboAnki

open SQLite

/-- The schema version this program writes (`PRAGMA user_version`). -/
def schemaVersion : Int64 := 1

def schema : String := "
CREATE TABLE decks (
  id INTEGER PRIMARY KEY AUTOINCREMENT,
  name TEXT NOT NULL UNIQUE,
  kind TEXT NOT NULL CHECK (kind IN ('flashcards', 'dictionary')),
  tag TEXT NOT NULL DEFAULT '',
  created_at INTEGER NOT NULL
);

CREATE TABLE cards (
  id INTEGER PRIMARY KEY AUTOINCREMENT,
  deck_id INTEGER NOT NULL REFERENCES decks(id) ON DELETE CASCADE,
  front TEXT NOT NULL,
  back TEXT NOT NULL,
  state INTEGER NOT NULL DEFAULT 0 CHECK (state BETWEEN 0 AND 3),
  due INTEGER,
  stability REAL NOT NULL DEFAULT 0,
  difficulty REAL NOT NULL DEFAULT 0,
  elapsed_days INTEGER NOT NULL DEFAULT 0 CHECK (elapsed_days >= 0),
  scheduled_days INTEGER NOT NULL DEFAULT 0 CHECK (scheduled_days >= 0),
  reps INTEGER NOT NULL DEFAULT 0 CHECK (reps >= 0),
  lapses INTEGER NOT NULL DEFAULT 0 CHECK (lapses >= 0),
  last_review INTEGER,
  created_at INTEGER NOT NULL,
  CHECK ((state = 0 AND due IS NULL AND last_review IS NULL)
      OR (state <> 0 AND due IS NOT NULL AND last_review IS NOT NULL))
);

CREATE UNIQUE INDEX cards_deck_front ON cards(deck_id, front);
CREATE INDEX cards_deck_state_due ON cards(deck_id, state, due);

CREATE TABLE reviews (
  id INTEGER PRIMARY KEY AUTOINCREMENT,
  card_id INTEGER NOT NULL REFERENCES cards(id) ON DELETE CASCADE,
  rating INTEGER NOT NULL CHECK (rating BETWEEN 1 AND 4),
  state INTEGER NOT NULL CHECK (state BETWEEN 0 AND 3),
  due INTEGER NOT NULL,
  stability REAL NOT NULL,
  difficulty REAL NOT NULL,
  elapsed_days INTEGER NOT NULL,
  scheduled_days INTEGER NOT NULL,
  reviewed_at INTEGER NOT NULL
);

CREATE INDEX reviews_card ON reviews(card_id);
"

/-- A row of the `cards` table, as stored. -/
structure CardRow where
  id : Int64
  deckId : Int64
  front : String
  back : String
  state : Int64
  due : Option Int64
  stability : Float
  difficulty : Float
  elapsedDays : Int64
  scheduledDays : Int64
  reps : Int64
  lapses : Int64
  lastReview : Option Int64
deriving Repr, SQLite.Row

def cardColumns : String :=
  "id, deck_id, front, back, state, due, stability, difficulty, elapsed_days, scheduled_days, " ++
  "reps, lapses, last_review"

def toNat (i : Int64) : Nat := i.toInt.toNat

def instant (i : Int64) : Instant := ⟨toNat i⟩

/-- The scheduling columns of a card row. -/
structure SchedColumns where
  state : Int64
  due : Option Int64
  stability : Float
  difficulty : Float
  elapsedDays : Int64
  scheduledDays : Int64
  reps : Int64
  lapses : Int64
  lastReview : Option Int64

def CardRow.schedColumns (r : CardRow) : SchedColumns :=
  { state := r.state, due := r.due, stability := r.stability, difficulty := r.difficulty,
    elapsedDays := r.elapsedDays, scheduledDays := r.scheduledDays, reps := r.reps,
    lapses := r.lapses, lastReview := r.lastReview }

/-- How the store writes a schedule. -/
def Sched.toColumns : Sched → SchedColumns
  | .new =>
    { state := 0, due := none, stability := 0, difficulty := 0, elapsedDays := 0,
      scheduledDays := 0, reps := 0, lapses := 0, lastReview := none }
  | .seen c =>
    { state := Int64.ofNat c.phase.code, due := some (Int64.ofNat c.due.ms),
      stability := c.stability, difficulty := c.difficulty,
      elapsedDays := Int64.ofNat c.elapsedDays, scheduledDays := Int64.ofNat c.scheduledDays,
      reps := Int64.ofNat c.reps, lapses := Int64.ofNat c.lapses,
      lastReview := some (Int64.ofNat c.lastReview.ms) }

/-- How the store reads a schedule back, rejecting columns `Sched` cannot represent. -/
def Sched.ofColumns (c : SchedColumns) : Except String Sched :=
  match c.state, c.due, c.lastReview with
  | 0, none, none => .ok .new
  | state, some due, some last =>
    match Phase.ofCode? (toNat state) with
    | some phase =>
      .ok <| .seen
        { phase, due := instant due, stability := c.stability, difficulty := c.difficulty,
          elapsedDays := toNat c.elapsedDays, scheduledDays := toNat c.scheduledDays,
          reps := toNat c.reps, lapses := toNat c.lapses, lastReview := instant last }
    | none => .error s!"invalid state {state}"
  | state, _, _ => .error s!"state {state} with an inconsistent due date"

/-- Decodes a stored card, rejecting rows its type cannot represent. -/
def Card.ofRow (r : CardRow) : Except String Card :=
  match Sched.ofColumns r.schedColumns with
  | .ok sched => .ok { id := ⟨r.id⟩, deckId := ⟨r.deckId⟩, front := r.front, back := r.back, sched }
  | .error msg => .error s!"card {r.id}: {msg}"

/-- The row the store keeps for a card. -/
def Card.toRow (c : Card) : CardRow :=
  let s := c.sched.toColumns
  { id := c.id.val, deckId := c.deckId.val, front := c.front, back := c.back, state := s.state,
    due := s.due, stability := s.stability, difficulty := s.difficulty,
    elapsedDays := s.elapsedDays, scheduledDays := s.scheduledDays, reps := s.reps,
    lapses := s.lapses, lastReview := s.lastReview }

/-- A row of the deck overview. -/
structure DeckRow where
  id : Int64
  name : String
  kind : String
  tag : String
  total : Int64
  due : Int64
  new : Int64
deriving SQLite.Row

/-- A connection to the database. -/
structure Store where
  db : SQLite

/-- Failures the user can do something about (as opposed to a broken database). -/
inductive StoreError where
  | duplicateDeck (name : String)
  | duplicateCard (front : String)
  | invalid (msg : String)
deriving Repr, Inhabited

def StoreError.message : StoreError → String
  | .duplicateDeck name => s!"There is already a deck called “{name}”."
  | .duplicateCard front => s!"This deck already has a card “{front}”."
  | .invalid msg => msg

namespace Store

/-- A violated `UNIQUE` constraint. (leansqlite lowercases the start of SQLite's message,
so the comparison ignores case.) -/
private def isUniqueViolation (e : IO.Error) : Bool :=
  ((toString e).toLower.splitOn "unique constraint failed").length > 1

private def all {α : Type} [Row α] (stmt : Stmt) : IO (Array α) := stmt.results.toArray

private def i64 (n : Nat) : Int64 := Int64.ofNat n

private def userVersion (db : SQLite) : IO Int64 := do
  let stmt ← db.prepare "PRAGMA user_version"
  if ← stmt.step then stmt.columnInt64 0 else pure 0

/-- Opens (creating if need be) the database at `path`. -/
def openAt (path : System.FilePath) : IO Store := do
  if let some dir := path.parent then
    if !dir.toString.isEmpty then IO.FS.createDirAll dir
  let db ← SQLite.open path (busyTimeoutMs := 5000)
  db.exec "PRAGMA foreign_keys = ON"
  db.exec "PRAGMA journal_mode = WAL"
  let v ← userVersion db
  if v == 0 then
    db.transaction do
      db.exec schema
      db.exec s!"PRAGMA user_version = {schemaVersion}"
  else if v > schemaVersion then
    throw <| IO.userError s!"{path} was written by a newer turbo-anki (schema {v})"
  return ⟨db⟩

/-- The default location: `$TURBO_ANKI_DB`, else `$XDG_DATA_HOME/turbo-anki/turbo-anki.db`
(`~/.local/share/turbo-anki/turbo-anki.db`). -/
def defaultPath : IO System.FilePath := do
  if let some p ← IO.getEnv "TURBO_ANKI_DB" then return p
  let base ← match ← IO.getEnv "XDG_DATA_HOME" with
    | some d => pure (System.FilePath.mk d)
    | none =>
      match ← IO.getEnv "HOME" with
      | some h => pure (System.FilePath.mk h / ".local" / "share")
      | none => throw <| IO.userError "cannot find the home directory; set TURBO_ANKI_DB"
  return base / "turbo-anki" / "turbo-anki.db"

/-! ## Decks -/

private def deckOfRow (r : DeckRow) : IO (Deck × DeckStats) := do
  let some kind := DeckKind.ofCode? r.kind
    | throw <| IO.userError s!"deck {r.id} has an unknown kind {r.kind}"
  return ({ id := ⟨r.id⟩, name := r.name, kind, tag := r.tag },
          { total := toNat r.total, due := toNat r.due, new := toNat r.new })

/-- Every deck with its counts at `now`, by name. -/
def decks (s : Store) (now : Instant) : IO (Array (Deck × DeckStats)) := do
  let stmt ← s.db sql!"SELECT d.id, d.name, d.kind, d.tag, COUNT(c.id),
      COALESCE(SUM(CASE WHEN c.state != 0 AND c.due <= {i64 now.ms} THEN 1 ELSE 0 END), 0),
      COALESCE(SUM(CASE WHEN c.state = 0 THEN 1 ELSE 0 END), 0)
    FROM decks d LEFT JOIN cards c ON c.deck_id = d.id
    GROUP BY d.id ORDER BY d.name COLLATE NOCASE"
  (← all (α := DeckRow) stmt).mapM deckOfRow

private def validName (name : String) : Except StoreError String :=
  let name := name.trimAscii.toString
  if name.isEmpty then .error (.invalid "A deck needs a name.") else .ok name

def deckNamed? (s : Store) (name : String) : IO (Option Deck) := do
  let stmt ← s.db sql!"SELECT id, name, kind, tag, 0, 0, 0 FROM decks WHERE name = {name}"
  match (← all (α := DeckRow) stmt)[0]? with
  | some r => return some (← deckOfRow r).1
  | none => return none

def createDeck (s : Store) (name : String) (kind : DeckKind) (now : Instant) (tag : String := "") :
    IO (Except StoreError DeckId) := do
  match validName name with
  | .error e => return .error e
  | .ok name =>
    try
      s.db exec!"INSERT INTO decks (name, kind, tag, created_at)
        VALUES ({name}, {kind.code}, {tag}, {i64 now.ms})"
      return .ok ⟨← s.db.lastInsertRowId⟩
    catch e =>
      if isUniqueViolation e then return .error (.duplicateDeck name) else throw e

def renameDeck (s : Store) (id : DeckId) (name : String) : IO (Except StoreError Unit) := do
  match validName name with
  | .error e => return .error e
  | .ok name =>
    try
      s.db exec!"UPDATE decks SET name = {name} WHERE id = {id.val}"
      return .ok ()
    catch e =>
      if isUniqueViolation e then return .error (.duplicateDeck name) else throw e

/-- Deletes a deck with all its cards and their review history. -/
def deleteDeck (s : Store) (id : DeckId) : IO Unit :=
  s.db exec!"DELETE FROM decks WHERE id = {id.val}"

/-! ## Cards -/

private def cards (stmt : Stmt) : IO (Array Card) := do
  (← all (α := CardRow) stmt).mapM fun r =>
    match Card.ofRow r with
    | .ok c => pure c
    | .error msg => throw (IO.userError msg)

def card? (s : Store) (id : CardId) : IO (Option Card) := do
  return (← cards (← s.db.prepare s!"SELECT {cardColumns} FROM cards WHERE id = {id.val}"))[0]?

/-- `%` and `_` match themselves in a search. -/
def likePattern (q : String) : String :=
  "%" ++ (q.toList.foldl (fun acc c =>
    if c == '%' || c == '_' || c == '\\' then acc.push '\\' |>.push c else acc.push c) "") ++ "%"

/-- The cards of a deck whose front or back contains `query` (all of them for an empty
query), by front. -/
def searchCards (s : Store) (deck : DeckId) (query : String) : IO (Array Card) := do
  let stmt ← s.db.prepare s!"SELECT {cardColumns} FROM cards
    WHERE deck_id = ?1 AND (front LIKE ?2 ESCAPE '\\' OR back LIKE ?2 ESCAPE '\\')
    ORDER BY front COLLATE NOCASE, id"
  stmt.bindInt64 1 deck.val
  stmt.bindText 2 (likePattern query.trimAscii.toString)
  cards stmt

/-- The cards for a session: due cards, most overdue first; or new cards — for a
dictionary the most recently added first, as melk does, for flashcards in the order
they were added. -/
def sessionCards (s : Store) (deck : Deck) (mode : Mode) (now : Instant) (limit : Nat) :
    IO (Array Card) := do
  match mode with
  | .review =>
    let stmt ← s.db.prepare s!"SELECT {cardColumns} FROM cards
      WHERE deck_id = ?1 AND state != 0 AND due <= ?2 ORDER BY due, id LIMIT ?3"
    stmt.bindInt64 1 deck.id.val
    stmt.bindInt64 2 (i64 now.ms)
    stmt.bindInt64 3 (i64 limit)
    cards stmt
  | .learn =>
    let order := if deck.kind == .dictionary then "DESC" else "ASC"
    let stmt ← s.db.prepare s!"SELECT {cardColumns} FROM cards
      WHERE deck_id = ?1 AND state = 0 ORDER BY id {order} LIMIT ?2"
    stmt.bindInt64 1 deck.id.val
    stmt.bindInt64 2 (i64 limit)
    cards stmt

private def validPair (front back : String) : Except StoreError Pair :=
  let front := front.trimAscii.toString
  let back := back.trimAscii.toString
  if front.isEmpty then .error (.invalid "The front is empty.")
  else if back.isEmpty then .error (.invalid "The back is empty.")
  else .ok { front, back }

def addCard (s : Store) (deck : DeckId) (front back : String) (now : Instant) :
    IO (Except StoreError CardId) := do
  match validPair front back with
  | .error e => return .error e
  | .ok p =>
    try
      s.db exec!"INSERT INTO cards (deck_id, front, back, created_at)
        VALUES ({deck.val}, {p.front}, {p.back}, {i64 now.ms})"
      return .ok ⟨← s.db.lastInsertRowId⟩
    catch e =>
      if isUniqueViolation e then return .error (.duplicateCard p.front) else throw e

/-- Changes a card's text; its schedule and history are kept. -/
def updateCard (s : Store) (id : CardId) (front back : String) : IO (Except StoreError Unit) := do
  match validPair front back with
  | .error e => return .error e
  | .ok p =>
    try
      s.db exec!"UPDATE cards SET front = {p.front}, back = {p.back} WHERE id = {id.val}"
      return .ok ()
    catch e =>
      if isUniqueViolation e then return .error (.duplicateCard p.front) else throw e

def deleteCard (s : Store) (id : CardId) : IO Unit :=
  s.db exec!"DELETE FROM cards WHERE id = {id.val}"


/-- Adds the pairs that are not in the deck yet (by front); returns how many were added. -/
def importPairs (s : Store) (deck : DeckId) (pairs : Array Pair) (now : Instant) : IO Nat :=
  s.db.transaction do
    let mut added := 0
    for p in pairs do
      s.db exec!"INSERT OR IGNORE INTO cards (deck_id, front, back, created_at)
        VALUES ({deck.val}, {p.front}, {p.back}, {i64 now.ms})"
      added := added + (← s.db.changes).toNatClampNeg
    return added

/-! ## Reviews -/

/-- Writes a card's schedule, encoded by `Sched.toColumns` (which `Sched.ofColumns`
provably decodes back). -/
private def writeSched (s : Store) (id : CardId) (sched : Sched) : IO Unit :=
  let c := sched.toColumns
  s.db exec!"UPDATE cards SET state = {c.state}, due = {c.due}, stability = {c.stability},
    difficulty = {c.difficulty}, elapsed_days = {c.elapsedDays}, scheduled_days = {c.scheduledDays},
    reps = {c.reps}, lapses = {c.lapses}, last_review = {c.lastReview}
    WHERE id = {id.val}"

private def writeLog (s : Store) (id : CardId) (l : ReviewLog) : IO Unit :=
  s.db exec!"INSERT INTO reviews (card_id, rating, state, due, stability, difficulty,
      elapsed_days, scheduled_days, reviewed_at)
    VALUES ({id.val}, {i64 l.rating.toNat}, {i64 l.stateBefore}, {i64 l.due.ms}, {l.stability},
      {l.difficulty}, {i64 l.elapsedDays}, {i64 l.scheduledDays}, {i64 l.reviewedAt.ms})"

/-- Records a review: schedules the card with FSRS and appends to its review log, in one
transaction. Returns the card as it is now. -/
def review (s : Store) (card : Card) (now : Instant) (r : Rating) : IO Card := do
  let next := Fsrs.next card.sched now r
  s.db.transaction do
    s.writeSched card.id (.seen next)
    s.writeLog card.id (Fsrs.log card.sched now r)
  return { card with sched := .seen next }

/-- Forgets a card's progress: it becomes new again (its review log is kept). -/
def resetCard (s : Store) (id : CardId) : IO Unit := s.writeSched id .new

/-! ## Migration from melk -/

/-- Inserts a card with its schedule and review history as they are (used by the melk
import; the caller runs it inside a transaction). Returns `false`, writing nothing, if
the deck already has a card with this front. -/
def insertWithHistory (s : Store) (deck : DeckId) (front back : String) (sched : Sched)
    (created : Instant) (history : Array ReviewLog) : IO Bool := do
  s.db exec!"INSERT OR IGNORE INTO cards (deck_id, front, back, created_at)
    VALUES ({deck.val}, {front}, {back}, {i64 created.ms})"
  if (← s.db.changes) == 0 then return false
  let id : CardId := ⟨← s.db.lastInsertRowId⟩
  s.writeSched id sched
  for l in history do s.writeLog id l
  return true

end Store

end TurboAnki
