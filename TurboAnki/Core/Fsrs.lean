import TurboAnki.Core.Time

/-!
# FSRS-5

The scheduler melk uses (`server/src/fsrs.ts`), ported line by line so that cards
migrated from melk carry on exactly where they were: FSRS-5 with the default
weights, 90 % requested retention and learning steps of a few minutes.

The types make the card lifecycle explicit: a card is either `new` (never reviewed,
so it has no due date and no memory state) or `seen` in one of three phases, and a
review always produces a `Seen` card. Theorems about the scheduler are in
`TurboAnki.Proofs.Fsrs`.
-/

namespace TurboAnki

/-- How well an answer was recalled. -/
inductive Rating where
  | again | hard | good | easy
deriving DecidableEq, Repr, Inhabited

namespace Rating

/-- The number FSRS (and the store) uses: `1‥4`. -/
def toNat : Rating → Nat
  | again => 1 | hard => 2 | good => 3 | easy => 4

def ofNat? : Nat → Option Rating
  | 1 => some again | 2 => some hard | 3 => some good | 4 => some easy
  | _ => none

def all : List Rating := [again, hard, good, easy]

def label : Rating → String
  | again => "Again" | hard => "Hard" | good => "Good" | easy => "Easy"

end Rating

/-- The phase of a card that has been reviewed at least once. -/
inductive Phase where
  | learning | review | relearning
deriving DecidableEq, Repr, Inhabited

/-- Scheduling state of a card that has been reviewed at least once. -/
structure Seen where
  phase : Phase
  due : Instant
  stability : Float
  difficulty : Float
  /-- Days between the last two reviews. -/
  elapsedDays : Nat
  /-- Days from the last review to `due`; zero during (re)learning steps. -/
  scheduledDays : Nat
  reps : Nat
  lapses : Nat
  lastReview : Instant
deriving Repr, Inhabited

/-- Scheduling state of a card. -/
inductive Sched where
  | new
  | seen (s : Seen)
deriving Repr, Inhabited

/-- What the review log records about one review. `stateBefore` is the card's state
code (see `Sched.code`) before the review; the rest describes the card after it. -/
structure ReviewLog where
  rating : Rating
  stateBefore : Nat
  due : Instant
  stability : Float
  difficulty : Float
  elapsedDays : Nat
  scheduledDays : Nat
  reviewedAt : Instant
deriving Repr, Inhabited

namespace Phase

/-- FSRS's state numbers: `1` learning, `2` review, `3` relearning. -/
def code : Phase → Nat
  | learning => 1 | review => 2 | relearning => 3

def ofCode? : Nat → Option Phase
  | 1 => some learning | 2 => some review | 3 => some relearning
  | _ => none

end Phase

namespace Sched

/-- FSRS's state number: `0` for a new card, else the phase's. -/
def code : Sched → Nat
  | new => 0
  | seen s => s.phase.code

def reps : Sched → Nat
  | new => 0
  | seen s => s.reps

def lapses : Sched → Nat
  | new => 0
  | seen s => s.lapses

end Sched

namespace Fsrs

/-- FSRS-5 default weights. -/
def W : Vector Float 19 := #v[
  0.40255, 1.18385, 3.173, 15.69105, 7.1949, 0.5345, 1.4604, 0.0046, 1.54575, 0.1192, 1.01925,
  1.9395, 0.11, 0.29605, 2.2698, 0.2315, 2.9898, 0.51655, 0.6621]

/-- Weight `i`. -/
@[inline] def w (i : Fin 19) : Float := W[i]

def requestRetention : Float := 0.9
def maximumInterval : Nat := 36500

def decay : Float := -0.5
/-- `0.9 ^ (1 / decay) - 1`, so that the retrievability after `stability` days is 90 %. -/
def factor : Float := 19 / 81

def retrievability (elapsedDays : Nat) (stability : Float) : Float :=
  (1 + factor * elapsedDays.toFloat / stability) ^ decay

/-- A whole number of days, at least one and at most `maximumInterval`. -/
def clampInterval (n : Nat) : Nat := min (max n 1) maximumInterval

/-- The interval at which recall probability falls to the requested retention. -/
def nextInterval (stability : Float) : Nat :=
  let raw := stability / factor * (requestRetention ^ (1 / decay) - 1)
  -- `toUInt64` saturates (and maps NaN to 0), so this is total; the clamp does the rest.
  clampInterval raw.round.toUInt64.toNat

def clampDifficulty (d : Float) : Float := min (max d 1) 10

def ratingValue (r : Rating) : Float := r.toNat.toFloat

def initStability (r : Rating) : Float :=
  let weight := match r with
    | .again => (w 0) | .hard => (w 1) | .good => (w 2) | .easy => (w 3)
  max weight 0.1

def initDifficulty (r : Rating) : Float :=
  clampDifficulty ((w 4) - Float.exp ((w 5) * (ratingValue r - 1)) + 1)

def nextDifficulty (d : Float) (r : Rating) : Float :=
  let delta := -(w 6) * (ratingValue r - 3)
  let damped := d + delta * (10 - d) / 9
  clampDifficulty ((w 7) * initDifficulty .easy + (1 - (w 7)) * damped)

def recallStability (d s retr : Float) (r : Rating) : Float :=
  let hardPenalty := if r = .hard then (w 15) else 1
  let easyBonus := if r = .easy then (w 16) else 1
  s * (1 + Float.exp (w 8) * (11 - d) * s ^ (-(w 9)) * (Float.exp ((w 10) * (1 - retr)) - 1) *
    hardPenalty * easyBonus)

def forgetStability (d s retr : Float) : Float :=
  min ((w 11) * d ^ (-(w 12)) * ((s + 1) ^ (w 13) - 1) * Float.exp ((w 14) * (1 - retr))) s

def shortTermStability (s : Float) (r : Rating) : Float :=
  s * Float.exp ((w 17) * (ratingValue r - 3 + (w 18)))

/-- The intervals for Hard, Good and Easy from the review phase, given the three
stabilities. They are forced apart so that a better rating never waits less. -/
def reviewIntervals (sHard sGood sEasy : Float) : Nat × Nat × Nat :=
  let hard := min (nextInterval sHard) (nextInterval sGood)
  let good := max (nextInterval sGood) (hard + 1)
  let easy := max (nextInterval sEasy) (good + 1)
  (hard, good, easy)

/-- Learning steps, in minutes, for a new card rated Again, Hard or Good. -/
def newStep : Rating → Nat
  | .again => 1 | .hard => 5 | _ => 10

/-- Learning steps, in minutes, for a (re)learning card rated Again or Hard. -/
def learningStep : Rating → Nat
  | .again => 5 | _ => 10

/-- Minutes until a card that lapsed in review comes back. -/
def relearnStep : Nat := 5

/-- The card's state after `rating` at `now`, before the review counters are updated. -/
structure Step where
  phase : Phase
  due : Instant
  stability : Float
  difficulty : Float
  scheduledDays : Nat
  lapses : Nat

/-- One step of the scheduler, by the card's state before the review. -/
def step (card : Sched) (now : Instant) (r : Rating) : Step :=
  match card with
  | .new =>
    let difficulty := initDifficulty r
    let stability := initStability r
    if r = .easy then
      let i := nextInterval stability
      { phase := .review, due := now.addDays i, stability, difficulty, scheduledDays := i, lapses := 0 }
    else
      { phase := .learning, due := now.addMinutes (newStep r), stability, difficulty,
        scheduledDays := 0, lapses := 0 }
  | .seen c =>
    match c.phase with
    | .learning | .relearning =>
      let difficulty := nextDifficulty c.difficulty r
      let stability := shortTermStability c.stability r
      if r = .again ∨ r = .hard then
        { phase := c.phase, due := now.addMinutes (learningStep r), stability, difficulty,
          scheduledDays := 0, lapses := c.lapses }
      else
        let i := nextInterval stability
        { phase := .review, due := now.addDays i, stability, difficulty, scheduledDays := i,
          lapses := c.lapses }
    | .review =>
      let retr := retrievability (Instant.daysBetween c.lastReview now) c.stability
      let difficulty := nextDifficulty c.difficulty r
      let sHard := recallStability difficulty c.stability retr .hard
      let sGood := recallStability difficulty c.stability retr .good
      let sEasy := recallStability difficulty c.stability retr .easy
      let (iHard, iGood, iEasy) := reviewIntervals sHard sGood sEasy
      match r with
      | .again =>
        { phase := .relearning, due := now.addMinutes relearnStep,
          stability := forgetStability difficulty c.stability retr, difficulty,
          scheduledDays := 0, lapses := c.lapses + 1 }
      | .hard =>
        { phase := .review, due := now.addDays iHard, stability := sHard, difficulty,
          scheduledDays := iHard, lapses := c.lapses }
      | .good =>
        { phase := .review, due := now.addDays iGood, stability := sGood, difficulty,
          scheduledDays := iGood, lapses := c.lapses }
      | .easy =>
        { phase := .review, due := now.addDays iEasy, stability := sEasy, difficulty,
          scheduledDays := iEasy, lapses := c.lapses }

/-- Days since the previous review, as FSRS counts them (zero for a new card). -/
def elapsed (card : Sched) (now : Instant) : Nat :=
  match card with
  | .new => 0
  | .seen c => Instant.daysBetween c.lastReview now

/-- Schedules the next review of `card`, rated `r` at `now`. -/
def next (card : Sched) (now : Instant) (r : Rating) : Seen :=
  let s := step card now r
  { phase := s.phase, due := s.due, stability := s.stability, difficulty := s.difficulty,
    elapsedDays := elapsed card now, scheduledDays := s.scheduledDays, reps := card.reps + 1,
    lapses := s.lapses, lastReview := now }

/-- The review log entry for rating `card` with `r` at `now`. -/
def log (card : Sched) (now : Instant) (r : Rating) : ReviewLog :=
  let c := next card now r
  { rating := r, stateBefore := card.code, due := c.due, stability := c.stability,
    difficulty := c.difficulty, elapsedDays := c.elapsedDays, scheduledDays := c.scheduledDays,
    reviewedAt := now }

end Fsrs

end TurboAnki
