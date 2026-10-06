import TurboAnki.Store
import TurboAnki.Proofs.Fsrs

/-!
# The store: theorems

What the store writes for a card, it reads back as the very same card: the encoding of
schedules into columns (`Sched.toColumns`, used by every write) and the decoding
(`Sched.ofColumns`, used by every read) are inverse. The only condition is that the
numbers fit the database's 64-bit integers, which instants (milliseconds until the
year 292 million) and counters do.

Deck kinds round-trip too (`DeckKind.ofCode?_code`, in `TurboAnki.Core.Model`).
-/

namespace TurboAnki

/-- Every number in a schedule fits a signed 64-bit integer. -/
def Sched.Fits : Sched → Prop
  | .new => True
  | .seen c => c.due.ms < 2 ^ 63 ∧ c.lastReview.ms < 2 ^ 63 ∧ c.elapsedDays < 2 ^ 63 ∧
      c.scheduledDays < 2 ^ 63 ∧ c.reps < 2 ^ 63 ∧ c.lapses < 2 ^ 63

theorem toNat_ofNat {n : Nat} (h : n < 2 ^ 63) : toNat (Int64.ofNat n) = n := by
  simp [toNat, Int64.toInt_ofNat_of_lt h]

theorem Phase.code_lt (p : Phase) : p.code < 2 ^ 63 := by
  cases p <;> decide

/-- **Schedules survive the store unchanged.** -/
theorem Sched.ofColumns_toColumns (s : Sched) (h : s.Fits) : Sched.ofColumns s.toColumns = .ok s := by
  cases s with
  | new => rfl
  | seen c =>
    obtain ⟨hdue, hlast, hel, hsch, hreps, hlapses⟩ := h
    simp only [Sched.toColumns, Sched.ofColumns, toNat_ofNat (Phase.code_lt _), Phase.ofCode?_code,
      instant, toNat_ofNat hdue, toNat_ofNat hlast, toNat_ofNat hel, toNat_ofNat hsch,
      toNat_ofNat hreps, toNat_ofNat hlapses]

/-- **Cards survive the store unchanged.** -/
theorem Card.ofRow_toRow (c : Card) (h : c.sched.Fits) : Card.ofRow c.toRow = .ok c := by
  have hs := Sched.ofColumns_toColumns c.sched h
  have : c.toRow.schedColumns = c.sched.toColumns := rfl
  simp only [Card.ofRow, this, hs]
  rfl

end TurboAnki
