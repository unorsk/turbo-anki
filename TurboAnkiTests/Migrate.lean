import TurboAnki

/-!
# Migration from melk

A dump in the shape `wrangler d1 export` writes, on melk's own schema
(`melk2/server/schema.sql`): two decks, cards in every state, a review log, and one
card no valid melk could have produced.
-/

namespace TurboAnkiTests.Migrate

open TurboAnki

def melkSchema : String := "
CREATE TABLE decks (id INTEGER PRIMARY KEY AUTOINCREMENT, name TEXT NOT NULL UNIQUE,
  tag TEXT NOT NULL DEFAULT '', created_at TEXT NOT NULL DEFAULT (strftime('%Y-%m-%dT%H:%M:%fZ', 'now')));
CREATE TABLE cards (id INTEGER PRIMARY KEY AUTOINCREMENT,
  deck_id INTEGER NOT NULL REFERENCES decks(id) ON DELETE CASCADE, front TEXT NOT NULL, back TEXT NOT NULL,
  state INTEGER NOT NULL DEFAULT 0, due TEXT, stability REAL NOT NULL DEFAULT 0,
  difficulty REAL NOT NULL DEFAULT 0, elapsed_days INTEGER NOT NULL DEFAULT 0,
  scheduled_days INTEGER NOT NULL DEFAULT 0, reps INTEGER NOT NULL DEFAULT 0,
  lapses INTEGER NOT NULL DEFAULT 0, last_review TEXT,
  created_at TEXT NOT NULL DEFAULT (strftime('%Y-%m-%dT%H:%M:%fZ', 'now')));
CREATE TABLE reviews (id INTEGER PRIMARY KEY AUTOINCREMENT,
  card_id INTEGER NOT NULL REFERENCES cards(id) ON DELETE CASCADE, rating INTEGER NOT NULL,
  state INTEGER NOT NULL, due TEXT NOT NULL, stability REAL NOT NULL, difficulty REAL NOT NULL,
  elapsed_days INTEGER NOT NULL, scheduled_days INTEGER NOT NULL, reviewed_at TEXT NOT NULL);
"

def melkData : String := "
PRAGMA defer_foreign_keys=TRUE;
INSERT INTO decks VALUES(1,'norsk','no','2026-07-13T10:00:00.000Z');
INSERT INTO decks VALUES(2,'deutsch','','2026-07-14T10:00:00.000Z');
INSERT INTO cards VALUES(1,1,'hund','dog',2,'2026-08-20T12:00:00.000Z',4.5,5.2,3,4,2,0,'2026-08-16T12:00:00.000Z','2026-07-13T10:00:00.000Z');
INSERT INTO cards VALUES(2,1,'får','sheep',0,NULL,0,0,0,0,0,0,NULL,'2026-07-13T10:00:00.000Z');
INSERT INTO cards VALUES(3,1,'katt','cat',3,'2026-08-16T12:05:00.000Z',1.0,7.6,7,0,3,1,'2026-08-16T12:00:00.000Z','2026-07-13T10:00:00.000Z');
INSERT INTO cards VALUES(4,2,'Hund','dog',1,'2030-01-01T00:00:00.000Z',3.1,5.3,0,0,1,0,'2026-08-16T12:00:00.000Z','2026-07-14T10:00:00.000Z');
INSERT INTO cards VALUES(5,2,'kaputt','broken',2,NULL,1,1,0,0,1,0,NULL,'2026-07-14T10:00:00.000Z');
INSERT INTO reviews VALUES(1,1,3,0,'2026-08-12T12:10:00.000Z',3.173,5.28,0,0,'2026-08-12T12:00:00.000Z');
INSERT INTO reviews VALUES(2,1,3,1,'2026-08-16T12:00:00.000Z',4.5,5.2,0,4,'2026-08-12T12:10:00.000Z');
INSERT INTO reviews VALUES(3,3,1,2,'2026-08-16T12:05:00.000Z',1.0,7.6,7,0,'2026-08-16T12:00:00.000Z');
"

def expect (ok : Bool) (msg : String) : IO Unit :=
  unless ok do throw <| IO.userError s!"migration test failed: {msg}"

def run (dir : System.FilePath) : IO Unit := do
  let dump := dir / "melk.sql"
  IO.FS.writeFile dump (melkSchema ++ melkData)
  let store ← Store.openAt (dir / "migrated.db")
  let now ← Instant.now
  let src ← TurboAnki.Migrate.openSource dump
  let r ← TurboAnki.Migrate.run src store now
  expect (r.decksCreated == 2 && r.cards == 4 && r.reviews == 3) s!"unexpected report: {r.summary}"
  expect (r.problems.size == 1) s!"the invalid card was not reported: {r.summary}"
  -- The schedule survives to the millisecond.
  let some norsk ← store.deckNamed? "norsk" | expect false "norsk missing"
  expect (norsk.kind == .dictionary && norsk.tag == "no") "the deck kind or tag is wrong"
  let hund := (← store.searchCards norsk.id "hund")[0]!
  match hund.sched with
  | .seen s =>
    expect (s.phase == .review && s.due.ms == 1787227200000 && s.lastReview.ms == 1786881600000 &&
      s.stability == 4.5 && s.scheduledDays == 4 && s.reps == 2) s!"hund was not migrated faithfully: {repr s}"
  | .new => expect false "hund became new"
  let far := (← store.searchCards norsk.id "får")[0]!
  expect (far.sched matches .new) "a new card did not stay new"
  -- melk and turbo-anki agree on what is due, deck by deck.
  let ours ← store.decks now
  for (name, total, due, new) in ← TurboAnki.Migrate.melkCounts src now do
    let some (_, s) := ours.find? (·.1.name == name) | expect false s!"{name} missing"
    -- The invalid card counts in melk's total but could not be imported.
    let total := if name == "deutsch" then total - 1 else total
    expect (s.total == total && s.due == due && s.new == new) s!"{name}: counts differ"
  -- Running it again changes nothing.
  let again ← TurboAnki.Migrate.run src store now
  expect (again.decksReused == 2 && again.cards == 0 && again.cardsSkipped == 4)
    s!"a second migration was not idempotent: {again.summary}"
  IO.println s!"migration: {r.summary.splitOn ";" |>.head!}; repeat is a no-op — passed"

end TurboAnkiTests.Migrate
