import Std.Time

/-!
# Time

Instants are milliseconds since the Unix epoch, the unit the store keeps. The
scheduler only ever adds whole minutes or days to an instant and counts whole days
between two, so no calendar is involved.
-/

namespace TurboAnki

/-- A point in time: milliseconds since the Unix epoch. -/
structure Instant where
  ms : Nat
deriving DecidableEq, Repr, Inhabited, Hashable

namespace Instant

instance : LT Instant := ⟨fun a b => a.ms < b.ms⟩
instance : LE Instant := ⟨fun a b => a.ms ≤ b.ms⟩
instance (a b : Instant) : Decidable (a < b) := inferInstanceAs (Decidable (a.ms < b.ms))
instance (a b : Instant) : Decidable (a ≤ b) := inferInstanceAs (Decidable (a.ms ≤ b.ms))

def minuteMs : Nat := 60_000
def dayMs : Nat := 86_400_000

def addMinutes (t : Instant) (m : Nat) : Instant := ⟨t.ms + m * minuteMs⟩
def addDays (t : Instant) (d : Nat) : Instant := ⟨t.ms + d * dayMs⟩

/-- Whole days from `a` to `b`; zero if `b` is not later than `a` (a clock set back). -/
def daysBetween (a b : Instant) : Nat := (b.ms - a.ms) / dayMs

/-- The current wall-clock time. -/
def now : IO Instant := do
  let t ← Std.Time.Timestamp.now
  return ⟨t.toMillisecondsSinceUnixEpoch.toInt.toNat⟩

theorem lt_addMinutes (t : Instant) {m : Nat} (h : 0 < m) : t < t.addMinutes m := by
  show t.ms < t.ms + m * minuteMs
  have : 0 < m * minuteMs := Nat.mul_pos h (by decide)
  omega

theorem lt_addDays (t : Instant) {d : Nat} (h : 0 < d) : t < t.addDays d := by
  show t.ms < t.ms + d * dayMs
  have : 0 < d * dayMs := Nat.mul_pos h (by decide)
  omega

end Instant

/-- A length of time, for display: `45s`, `10m`, `3h`, `12d`, `4.5mo`, `2.1y`. -/
def formatSpan (ms : Nat) : String :=
  let s := ms / 1000
  let tenths (n d : Nat) : String :=
    let t := (n * 10 + d / 2) / d
    if t % 10 == 0 then s!"{t / 10}" else s!"{t / 10}.{t % 10}"
  if s < 60 then s!"{s}s"
  else if s < 3600 then s!"{s / 60}m"
  else if s < 86_400 then s!"{s / 3600}h"
  else if s < 30 * 86_400 then s!"{s / 86_400}d"
  else if s < 365 * 86_400 then s!"{tenths s (30 * 86_400)}mo"
  else s!"{tenths s (365 * 86_400)}y"

end TurboAnki
