import TurboAnki.Core.Grade

/-!
# Sessions

The two ways of studying a deck, as pure state machines over card identifiers `κ`.

**Drill** (dictionary decks, melk's typing drill). The session's cards, already
shuffled, are queued three times over. The first answer to a card is its FSRS rating;
the later passes are for memorizing. A wrong answer sends the card to the back of the
queue again, so by the end every card has been typed correctly (or nearly) three times.

**Study** (flashcard decks, Anki-like). Each card is rated by hand, every time it is
shown. A card that is still in its learning steps afterwards — due again within
minutes — goes to the back of the queue; a card that graduates leaves the session.

Theorems about both are in `TurboAnki.Proofs.Session`.
-/

namespace TurboAnki

/-- A typing drill in progress. -/
structure Drill (κ : Type) where
  /-- The session's cards, in the order of the first pass. -/
  cards : List κ
  /-- What is left to type; the head is the card being asked. -/
  pending : List κ
  /-- The first-attempt rating of each card answered so far, in the order answered. -/
  firstRatings : List (κ × Rating) := []
  /-- Every answer that was not wrong, newest first. -/
  passed : List κ := []
deriving Repr, Inhabited

namespace Drill

variable {κ : Type} [DecidableEq κ]

/-- Every card is typed correctly this many times. -/
def passes : Nat := 3

def start (cards : List κ) : Drill κ := { cards, pending := cards ++ cards ++ cards }

def current? (d : Drill κ) : Option κ := d.pending.head?

def isFinished (d : Drill κ) : Bool := d.pending.isEmpty

/-- The first-attempt rating of `c`, once it has been answered. -/
def ratingOf? (d : Drill κ) (c : κ) : Option Rating := d.firstRatings.lookup c

/-- Whether the next answer to `c` is its first, and so sets its rating. -/
def isFirstAttempt (d : Drill κ) (c : κ) : Bool := (d.ratingOf? c).isNone

/-- Which pass (`1‥3`) the card being asked is on: one more than its correct answers. -/
def pass (d : Drill κ) : Nat :=
  match d.current? with
  | some c => d.passed.count c + 1
  | none => passes

/-- Records the grade of the answer to the current card and moves on. -/
def answer (d : Drill κ) (g : Grade) : Drill κ :=
  match d.pending with
  | [] => d
  | c :: rest =>
    { d with
      pending := if g = .wrong then rest ++ [c] else rest
      firstRatings := if d.isFirstAttempt c then d.firstRatings ++ [(c, g.rating)] else d.firstRatings
      passed := if g = .wrong then d.passed else c :: d.passed }

end Drill

/-- A flashcard session in progress. -/
structure Study (κ : Type) where
  /-- Cards still to show; the head is the card being shown. -/
  pending : List κ
  /-- Answers given so far. -/
  answered : Nat := 0
deriving Repr, Inhabited

namespace Study

variable {κ : Type}

def start (cards : List κ) : Study κ := { pending := cards }

def current? (s : Study κ) : Option κ := s.pending.head?

def isFinished (s : Study κ) : Bool := s.pending.isEmpty

/-- Moves on after the current card was rated. A card that is still in its learning steps
(`graduated = false`) is shown again at the end of the session. -/
def answer (s : Study κ) (graduated : Bool) : Study κ :=
  match s.pending with
  | [] => s
  | c :: rest => { pending := if graduated then rest else rest ++ [c], answered := s.answered + 1 }

end Study

end TurboAnki
