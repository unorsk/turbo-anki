import TurboAnki.Core.Fsrs

/-!
# FSRS: theorems

Memory state (stability, difficulty) is floating-point arithmetic and is checked
against melk's implementation by tests instead (`TurboAnkiTests.Fsrs`). Everything a
learner relies on about *when* cards come back is proved here, for every card, time
and rating:

* a review always schedules the card strictly in the future;
* a card is in the review phase exactly when it is scheduled whole days ahead
  (between one day and a hundred years), and otherwise comes back within minutes;
* Again never schedules a card days ahead, Easy always does;
* from the review phase Hard waits less than Good, which waits less than Easy;
* each review counts one repetition, and only forgetting a card in review counts a
  lapse;
* the state codes and ratings the store keeps decode back to what was stored.
-/

namespace TurboAnki

theorem Rating.ofNat?_toNat (r : Rating) : Rating.ofNat? r.toNat = some r := by
  cases r <;> rfl

theorem Rating.toNat_le (r : Rating) : 1 ≤ r.toNat ∧ r.toNat ≤ 4 := by
  cases r <;> decide

theorem Phase.ofCode?_code (p : Phase) : Phase.ofCode? p.code = some p := by
  cases p <;> rfl

theorem Phase.code_pos (p : Phase) : 0 < p.code := by
  cases p <;> decide

theorem Sched.code_lt (c : Sched) : c.code < 4 := by
  cases c with
  | new => decide
  | seen s => cases h : s.phase <;> simp [Sched.code, h, Phase.code]

namespace Fsrs

theorem clampInterval_pos (n : Nat) : 1 ≤ clampInterval n := by
  simp only [clampInterval, maximumInterval]; omega

theorem clampInterval_le (n : Nat) : clampInterval n ≤ maximumInterval := by
  simp only [clampInterval, maximumInterval]; omega

theorem nextInterval_pos (s : Float) : 1 ≤ nextInterval s := clampInterval_pos _

theorem nextInterval_le (s : Float) : nextInterval s ≤ maximumInterval := clampInterval_le _

/-- From the review phase, Hard waits at least a day, less than Good, which waits less
than Easy; none waits more than a hundred years (and two days). -/
theorem reviewIntervals_spec (a b c : Float) :
    1 ≤ (reviewIntervals a b c).1 ∧ (reviewIntervals a b c).1 < (reviewIntervals a b c).2.1 ∧
      (reviewIntervals a b c).2.1 < (reviewIntervals a b c).2.2 ∧
      (reviewIntervals a b c).2.2 ≤ maximumInterval + 2 := by
  have := nextInterval_pos a; have := nextInterval_pos b
  have := nextInterval_le a; have := nextInterval_le b; have := nextInterval_le c
  simp only [reviewIntervals]
  omega

/-- The shape of every scheduling step: either the card is in the review phase and due
whole days ahead, or it is (re)learning and due within minutes. -/
theorem step_shape (c : Sched) (now : Instant) (r : Rating) :
    let s := step c now r
    (s.phase = .review ∧ 1 ≤ s.scheduledDays ∧ s.scheduledDays ≤ maximumInterval + 2 ∧
        s.due = now.addDays s.scheduledDays) ∨
      (s.phase ≠ .review ∧ s.scheduledDays = 0 ∧ ∃ m, 0 < m ∧ s.due = now.addMinutes m) := by
  intro s
  cases c with
  | new =>
    have := nextInterval_pos (initStability r)
    have := nextInterval_le (initStability r)
    cases r <;> simp [s, step, newStep] <;> first | omega | exact ⟨_, by decide, rfl⟩
  | seen c =>
    cases hp : c.phase with
    | learning | relearning =>
      have := nextInterval_pos (shortTermStability c.stability r)
      have := nextInterval_le (shortTermStability c.stability r)
      cases r <;> simp [s, step, hp, learningStep] <;> first | omega | exact ⟨_, by decide, rfl⟩
    | review =>
      simp only [s, step, hp]
      generalize hi : reviewIntervals _ _ _ = t
      have := reviewIntervals_spec
        (recallStability (nextDifficulty c.difficulty r) c.stability
          (retrievability (Instant.daysBetween c.lastReview now) c.stability) .hard)
        (recallStability (nextDifficulty c.difficulty r) c.stability
          (retrievability (Instant.daysBetween c.lastReview now) c.stability) .good)
        (recallStability (nextDifficulty c.difficulty r) c.stability
          (retrievability (Instant.daysBetween c.lastReview now) c.stability) .easy)
      rw [hi] at this
      obtain ⟨iHard, iGood, iEasy⟩ := t
      simp only at this
      cases r <;> simp [relearnStep] <;> first | omega | exact ⟨_, by decide, rfl⟩

/-- **A review always schedules the card strictly in the future.** -/
theorem next_due_gt (c : Sched) (now : Instant) (r : Rating) : now < (next c now r).due := by
  rcases step_shape c now r with ⟨_, h1, _, h2⟩ | ⟨_, _, m, hm, h2⟩
  · show now < (step c now r).due
    rw [h2]; exact Instant.lt_addDays now h1
  · show now < (step c now r).due
    rw [h2]; exact Instant.lt_addMinutes now hm

/-- **A card is in the review phase exactly when it is scheduled days ahead**; otherwise
it is in its (re)learning steps and comes back the same day. -/
theorem next_review_iff (c : Sched) (now : Instant) (r : Rating) :
    (next c now r).phase = .review ↔ 0 < (next c now r).scheduledDays := by
  rcases step_shape c now r with ⟨h0, h1, _⟩ | ⟨h0, h1, _⟩
  · exact ⟨fun _ => h1, fun _ => h0⟩
  · exact ⟨fun h => absurd h h0, fun h => by simp [next, h1] at h⟩

theorem next_scheduledDays_le (c : Sched) (now : Instant) (r : Rating) :
    (next c now r).scheduledDays ≤ maximumInterval + 2 := by
  rcases step_shape c now r with ⟨_, _, h, _⟩ | ⟨_, h, _⟩
  · exact h
  · show (step c now r).scheduledDays ≤ _
    rw [h]; exact Nat.zero_le _

/-- A review card is due `scheduledDays` after the review. -/
theorem next_due_review {c : Sched} {now : Instant} {r : Rating}
    (h : (next c now r).phase = .review) :
    (next c now r).due = now.addDays (next c now r).scheduledDays := by
  rcases step_shape c now r with ⟨_, _, _, h2⟩ | ⟨h0, _⟩
  · exact h2
  · exact absurd h h0

/-- **Again never schedules a card days ahead.** -/
theorem next_again_not_review (c : Sched) (now : Instant) :
    (next c now .again).phase ≠ .review := by
  cases c with
  | new => simp [next, step]
  | seen c => cases hp : c.phase <;> simp [next, step, hp]

/-- **Easy always schedules a card days ahead.** -/
theorem next_easy_review (c : Sched) (now : Instant) : (next c now .easy).phase = .review := by
  cases c with
  | new => simp [next, step]
  | seen c => cases hp : c.phase <;> simp [next, step, hp]

/-- Good graduates every card that has been seen before. -/
theorem next_good_review (c : Seen) (now : Instant) : (next (.seen c) now .good).phase = .review := by
  cases hp : c.phase <;> simp [next, step, hp]

/-- Forgetting a card in review sends it back to relearning. -/
theorem next_again_relearning {c : Seen} (hp : c.phase = .review) (now : Instant) :
    (next (.seen c) now .again).phase = .relearning := by
  simp [next, step, hp]

/-- Each review counts one repetition. -/
theorem next_reps (c : Sched) (now : Instant) (r : Rating) : (next c now r).reps = c.reps + 1 := rfl

/-- The review is recorded as the card's last. -/
theorem next_lastReview (c : Sched) (now : Instant) (r : Rating) : (next c now r).lastReview = now :=
  rfl

/-- **Only forgetting a card in review counts a lapse.** -/
theorem next_lapses (c : Sched) (now : Instant) (r : Rating) :
    (next c now r).lapses =
      c.lapses + (match c, r with | .seen s, .again => if s.phase = .review then 1 else 0 | _, _ => 0) := by
  cases c with
  | new => cases r <;> simp [next, step, Sched.lapses]
  | seen c => cases hp : c.phase <;> cases r <;> simp [next, step, hp, Sched.lapses]

/-- The log records the card's state before the review and its schedule after it. -/
theorem log_eq (c : Sched) (now : Instant) (r : Rating) :
    (log c now r).stateBefore = c.code ∧ (log c now r).due = (next c now r).due ∧
      (log c now r).scheduledDays = (next c now r).scheduledDays ∧ (log c now r).reviewedAt = now :=
  ⟨rfl, rfl, rfl, rfl⟩

end Fsrs

end TurboAnki
