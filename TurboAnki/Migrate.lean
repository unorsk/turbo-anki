import TurboAnki.Store

/-!
# Migrating from melk

melk keeps its data in a Cloudflare D1 database. `wrangler d1 export melk --remote
--output melk.sql` writes it out as SQL; this module reads such a dump (or a melk
SQLite database file) and copies every deck, card and review into the store, with the
full FSRS state, so that nothing is due earlier or later than it was in melk.

* melk decks are word lists studied by typing, so they become dictionary decks.
* melk stores times as ISO 8601 text; they are converted to milliseconds by SQLite's
  own date functions while reading.
* Every card goes through `Card.ofRow`, the decoder the store itself uses, so a card the
  store could not represent is reported rather than imported.
* Running it again is harmless: decks are matched by name and cards by their front, and
  what is already there is left alone.
-/

namespace TurboAnki.Migrate

open SQLite

structure MelkDeck where
  id : Int64
  name : String
  tag : String
deriving SQLite.Row

structure MelkReview where
  rating : Int64
  state : Int64
  due : Int64
  stability : Float
  difficulty : Float
  elapsedDays : Int64
  scheduledDays : Int64
  reviewedAt : Int64
deriving SQLite.Row

/-- ISO 8601 text (`2026-08-12T14:28:01.123Z`) as milliseconds since the epoch, in SQL. -/
def millis (column : String) : String :=
  s!"CAST(ROUND((julianday({column}) - 2440587.5) * 86400000) AS INTEGER)"

/-- What a migration did. -/
structure Report where
  decksCreated : Nat := 0
  decksReused : Nat := 0
  cards : Nat := 0
  cardsSkipped : Nat := 0
  reviews : Nat := 0
  problems : Array String := #[]
deriving Repr, Inhabited

def Report.summary (r : Report) : String :=
  s!"{r.decksCreated} deck(s) created, {r.decksReused} already there; " ++
  s!"{r.cards} card(s) with {r.reviews} review(s) imported, {r.cardsSkipped} already there" ++
  (if r.problems.isEmpty then "." else s!"; {r.problems.size} problem(s):\n  " ++
    "\n  ".intercalate r.problems.toList)

/-- Opens a melk database: a SQLite file as it is, or a SQL dump loaded into memory. -/
def openSource (path : System.FilePath) : IO SQLite := do
  let bytes ← IO.FS.readBinFile path
  if (bytes.extract 0 15) == "SQLite format 3".toUTF8 then
    return ← SQLite.openWith path .readonly
  let some sql := String.fromUTF8? bytes | throw <| IO.userError s!"{path} is not UTF-8 text"
  let db ← SQLite.open ":memory:"
  db.exec sql
  return db

private def all {α : Type} [Row α] (stmt : Stmt) : IO (Array α) := stmt.results.toArray

/-- Decodes one melk review into a log entry. -/
def MelkReview.toLog (r : MelkReview) : Except String ReviewLog := do
  let some rating := Rating.ofNat? r.rating.toInt.toNat | .error s!"invalid rating {r.rating}"
  if r.state < 0 || r.state > 3 then .error s!"invalid state {r.state}"
  return { rating, stateBefore := r.state.toInt.toNat, due := ⟨r.due.toInt.toNat⟩,
           stability := r.stability, difficulty := r.difficulty,
           elapsedDays := r.elapsedDays.toInt.toNat, scheduledDays := r.scheduledDays.toInt.toNat,
           reviewedAt := ⟨r.reviewedAt.toInt.toNat⟩ }

/-- Copies everything in the melk database `src` into `store`, in one transaction. -/
def run (src : SQLite) (store : Store) (now : Instant) : IO Report := do
  let decks ← all (α := MelkDeck) (← src.prepare "SELECT id, name, tag FROM decks ORDER BY id")
  store.db.transaction do
    let mut report : Report := {}
    for md in decks do
      let deck ← match ← store.deckNamed? md.name with
        | some d =>
          report := { report with decksReused := report.decksReused + 1 }
          if d.kind != .dictionary then
            report := { report with problems := (report.problems.push
              s!"deck {md.name} exists as a {d.kind.label.toLower} deck; its cards are added to it") }
          pure d.id
        | none =>
          match ← store.createDeck md.name .dictionary now md.tag with
          | .ok id =>
            report := { report with decksCreated := report.decksCreated + 1 }
            pure id
          | .error e => throw <| IO.userError e.message
      let stmt ← src.prepare s!"SELECT id, {md.id}, front, back, state, {millis "due"}, stability,
          difficulty, elapsed_days, scheduled_days, reps, lapses, {millis "last_review"},
          {millis "created_at"}
        FROM cards WHERE deck_id = ?1 ORDER BY id"
      stmt.bindInt64 1 md.id
      while ← stmt.step do
        let row : CardRow ← (Row.read : RowReader CardRow).run stmt
        let created ← stmt.columnInt64 13
        match Card.ofRow row with
        | .error msg =>
          report := { report with problems := report.problems.push s!"{md.name}/{row.front}: {msg}" }
        | .ok card =>
          let rs ← src.prepare s!"SELECT rating, state, {millis "due"}, stability, difficulty,
              elapsed_days, scheduled_days, {millis "reviewed_at"}
            FROM reviews WHERE card_id = ?1 ORDER BY reviewed_at, id"
          rs.bindInt64 1 row.id
          let mut logs := #[]
          for r in ← all (α := MelkReview) rs do
            match r.toLog with
            | .ok l => logs := logs.push l
            | .error msg =>
              report := { report with problems := (report.problems.push
                s!"{md.name}/{row.front}: review skipped: {msg}") }
          if ← store.insertWithHistory deck card.front card.back card.sched ⟨created.toInt.toNat⟩ logs then
            report := { report with cards := report.cards + 1, reviews := report.reviews + logs.size }
          else
            report := { report with cardsSkipped := report.cardsSkipped + 1 }
    return report

/-- Per deck: cards, cards due at `now`, new cards — as melk counts them, from the source. -/
def melkCounts (src : SQLite) (now : Instant) : IO (Array (String × Nat × Nat × Nat)) := do
  let stmt ← src.prepare s!"SELECT d.name, COUNT(c.id),
      COALESCE(SUM(CASE WHEN c.state != 0 AND {millis "c.due"} <= ?1 THEN 1 ELSE 0 END), 0),
      COALESCE(SUM(CASE WHEN c.state = 0 THEN 1 ELSE 0 END), 0)
    FROM decks d LEFT JOIN cards c ON c.deck_id = d.id GROUP BY d.id ORDER BY d.name"
  stmt.bindInt64 1 (Int64.ofNat now.ms)
  let mut out := #[]
  while ← stmt.step do
    out := out.push ((← stmt.columnText 0), (← stmt.columnInt64 1).toInt.toNat,
      (← stmt.columnInt64 2).toInt.toNat, (← stmt.columnInt64 3).toInt.toNat)
  return out

end TurboAnki.Migrate
