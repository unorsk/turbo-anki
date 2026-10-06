import TurboAnki

/-!
# FSRS against melk

Golden vectors produced by melk's own scheduler (`scripts/fsrs_golden.ts` running
`melk2/server/src/fsrs.ts`): four review sequences, and after each review the card's
state, time until due, stability, difficulty, elapsed and scheduled days, reps and
lapses. The port must agree exactly on everything but the floating-point memory state,
which must agree to six decimals.
-/

namespace TurboAnkiTests

open TurboAnki

/-- `(state, ms until due, stability, difficulty, elapsed days, scheduled days, reps, lapses)`. -/
abbrev Expected := Nat × Nat × Float × Float × Nat × Nat × Nat × Nat

def start : Instant := ⟨1767225600000⟩ -- 2026-01-01T00:00:00Z

/-- Runs a sequence of `(minutes after the previous review, rating)` and compares. -/
def agrees (seq : List (Nat × Nat)) (expected : List Expected) : Bool := Id.run do
  let mut card : Sched := .new
  let mut t := start
  let mut ok := seq.length == expected.length
  for ((mins, r), (state, dueIn, stab, diff, el, sch, reps, lapses)) in seq.zip expected do
    t := t.addMinutes mins
    let some rating := Rating.ofNat? r | return false
    let c := Fsrs.next card t rating
    card := .seen c
    let close (a b : Float) := (a - b).abs < 5e-6
    ok := ok && c.phase.code == state && c.due.ms - t.ms == dueIn && close c.stability stab &&
      close c.difficulty diff && c.elapsedDays == el && c.scheduledDays == sch && c.reps == reps &&
      c.lapses == lapses
  return ok

def day : Nat := 60 * 24

#guard agrees [(0, 3), (10, 3), (day * 3, 3), (day * 10, 3), (day * 30, 3)]
  [(1, 600000, 3.173000, 5.282434, 0, 0, 1, 0),
   (2, 345600000, 4.466858, 5.272968, 0, 4, 2, 0),
   (2, 1036800000, 11.963690, 5.263545, 3, 12, 3, 0),
   (2, 2937600000, 33.843327, 5.254165, 10, 34, 4, 0),
   (2, 7948800000, 91.623909, 5.244829, 30, 92, 5, 0)]

#guard agrees [(0, 1), (1, 1), (5, 2), (10, 3), (day * 2, 1), (5, 3), (day * 1, 4)]
  [(1, 60000, 0.402550, 7.194900, 0, 0, 1, 0),
   (1, 300000, 0.201689, 8.082797, 0, 0, 2, 0),
   (1, 600000, 0.169387, 8.370116, 0, 0, 3, 0),
   (2, 86400000, 0.238458, 8.346446, 0, 1, 4, 0),
   (3, 300000, 0.238458, 8.857050, 2, 0, 5, 1),
   (2, 86400000, 0.335694, 8.831140, 0, 1, 6, 1),
   (2, 345600000, 3.758007, 8.616555, 1, 4, 7, 1)]

#guard agrees [(0, 4), (day * 20, 2), (day * 5, 3), (day * 40, 4)]
  [(2, 1382400000, 15.691050, 3.224502, 0, 16, 1, 0),
   (2, 2332800000, 26.606077, 4.318882, 20, 27, 2, 0),
   (2, 3369600000, 39.016131, 4.313848, 5, 39, 3, 0),
   (2, 28857600000, 334.271954, 3.390408, 40, 334, 4, 0)]

#guard agrees [(0, 2), (5, 3), (day * 7, 1), (5, 1), (5, 2), (10, 3), (day * 365, 3)]
  [(1, 300000, 1.183850, 6.488305, 0, 0, 1, 0),
   (2, 172800000, 1.666590, 6.473292, 0, 2, 2, 0),
   (3, 300000, 1.010352, 7.597617, 7, 0, 3, 1),
   (3, 300000, 0.506215, 8.353568, 0, 0, 4, 1),
   (3, 600000, 0.425140, 8.595906, 0, 0, 5, 1),
   (2, 86400000, 0.598500, 8.571198, 0, 1, 6, 1),
   (2, 1036800000, 11.916943, 8.546603, 365, 12, 7, 1)]

end TurboAnkiTests
