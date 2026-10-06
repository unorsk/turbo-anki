import TurboAnki.Core.Grade
import TurboAnki.Proofs.Distance

/-!
# Grading: theorems

* An answer is correct exactly when it is non-empty and agrees with the expected
  answer after normalization (case, punctuation and spacing ignored, accents kept) —
  equivalently, when it is at edit distance zero.
* Typing the expected answer is always correct; an empty answer is always wrong.
* A typo is close: it differs only in accents, or is at most two edits away and so at
  most two characters longer or shorter than the expected answer.
* Typing cannot earn Easy, and only a wrong answer earns Again.
-/

namespace TurboAnki

open Text Distance

theorem Grade.rating_ne_easy (g : Grade) : g.rating ≠ .easy := by
  cases g <;> decide

theorem Grade.rating_eq_again_iff (g : Grade) : g.rating = .again ↔ g = .wrong := by
  cases g <;> decide

theorem grade_eq_correct_iff (input expected : String) :
    grade input expected = .correct ↔ normalize input ≠ [] ∧ normalize input = normalize expected := by
  unfold grade Grade.ofNormalized
  generalize normalize input = a
  generalize normalize expected = t
  by_cases ha : a = [] <;> by_cases hat : a = t <;> simp only [ha, hat] <;>
    (repeat' split) <;> simp_all

/-- Correct means at edit distance zero from the expected answer. -/
theorem grade_eq_correct_iff_osa (input expected : String) :
    grade input expected = .correct ↔
      normalize input ≠ [] ∧ osa (normalize input) (normalize expected) = 0 := by
  rw [grade_eq_correct_iff, osa_eq_zero_iff]

/-- Typing the expected answer is correct. -/
theorem grade_self (expected : String) (h : normalize expected ≠ []) :
    grade expected expected = .correct :=
  (grade_eq_correct_iff _ _).2 ⟨h, rfl⟩

/-- An answer with nothing in it (after dropping punctuation and spaces) is wrong. -/
theorem grade_empty {input : String} (h : normalize input = []) (expected : String) :
    grade input expected = .wrong := by
  simp [grade, Grade.ofNormalized, h]

theorem tolerance_le_two (n : Nat) : Grade.tolerance n ≤ 2 := by
  unfold Grade.tolerance; split <;> omega

/-- **A typo is close to the answer**: it differs only in accents, or it is within two
edits, and so within two characters of the answer's length. -/
theorem grade_typo {input expected : String} (h : grade input expected = .typo) :
    stripAccents (normalize input) = stripAccents (normalize expected) ∨
      (osa (normalize input) (normalize expected) ≤ 2 ∧
        (normalize input).length ≤ (normalize expected).length + 2 ∧
        (normalize expected).length ≤ (normalize input).length + 2) := by
  unfold grade Grade.ofNormalized at h
  generalize normalize input = a at h ⊢
  generalize normalize expected = t at h ⊢
  have hl := length_sub_le_osa a t
  have := tolerance_le_two t.length
  split at h
  · simp at h
  split at h
  · simp at h
  split at h
  · exact .inl ‹_›
  split at h
  · exact .inr ⟨by omega, by omega, by omega⟩
  · simp at h

/-- On short words (up to four letters) a typo is a single edit, or an accent slip. -/
theorem grade_typo_short {input expected : String} (h : grade input expected = .typo)
    (hs : (normalize expected).length ≤ 4) :
    stripAccents (normalize input) = stripAccents (normalize expected) ∨
      osa (normalize input) (normalize expected) ≤ 1 := by
  unfold grade Grade.ofNormalized at h
  generalize normalize input = a at h ⊢
  generalize normalize expected = t at h hs ⊢
  split at h
  · simp at h
  split at h
  · simp at h
  split at h
  · exact .inl ‹_›
  split at h
  · right; simpa [Grade.tolerance, hs] using ‹osa a t ≤ Grade.tolerance t.length›
  · simp at h

end TurboAnki
