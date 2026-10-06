import TurboAnki.Core.Fsrs
import TurboAnki.Core.Text
import TurboAnki.Core.Distance

/-!
# Grading typed answers

melk's rules: an exact answer (after `Text.normalize`) is correct; a near miss is a
typo; anything else is wrong. A near miss is an answer that differs only in its
accents, or is within one edit of a word of up to four letters and two edits of a
longer one. A swap of two adjacent letters counts as one edit.

The grade of a card's first attempt is its FSRS rating, so the rating is computed
rather than asked for: correct is Good, a typo Hard, wrong Again. Easy cannot be
expressed by typing.
-/

namespace TurboAnki

/-- Outcome of grading one typed answer. -/
inductive Grade where
  | correct | typo | wrong
deriving DecidableEq, Repr, Inhabited

namespace Grade

/-- The FSRS rating a grade earns on a card's first attempt. -/
def rating : Grade → Rating
  | correct => .good
  | typo => .hard
  | wrong => .again

/-- How far off a word of `length` characters may be and still count as a typo. Two edits
reach an unrelated word when it is short. -/
def tolerance (length : Nat) : Nat := if length ≤ 4 then 1 else 2

/-- Grades a normalized answer `a` against the normalized expected text `t`. -/
def ofNormalized (a t : List Char) : Grade :=
  if a.isEmpty then wrong
  else if a = t then correct
  else if Text.stripAccents a = Text.stripAccents t then typo
  else if Distance.osa a t ≤ tolerance t.length then typo
  else wrong

end Grade

/-- Grades the typed `input` against the `expected` answer. -/
def grade (input expected : String) : Grade :=
  Grade.ofNormalized (Text.normalize input) (Text.normalize expected)

end TurboAnki
