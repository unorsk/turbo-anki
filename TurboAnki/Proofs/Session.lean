import TurboAnki.Core.Session
import TurboAnki.Core.Shuffle

/-!
# Sessions: theorems

**Shuffling** only reorders: a shuffled session has exactly the cards it was given.

**Drill.** Throughout a drill:

* each card's correct answers plus its remaining appearances in the queue are always
  three (for each time it is in the session) — so a finished drill has had every card
  typed correctly exactly three times;
* each card gets exactly one rating, from its first answer, and it never changes;
* the queue only ever holds the session's cards;
* a correct answer shortens the queue by one, a wrong one leaves its length alone.

At the end every card of the session has a rating, so every card gets its FSRS review.

**Study.** A rated card leaves the session exactly when it graduates; otherwise it is
queued again, and the session never gains cards.
-/

namespace TurboAnki

/-! ## Shuffling -/

theorem getElem_cons_eraseIdx_perm {α : Type} (l : List α) (i : Nat) (h : i < l.length) :
    (l[i] :: l.eraseIdx i).Perm l := by
  rw [List.eraseIdx_eq_take_drop_succ]
  conv => rhs; rw [← List.take_append_drop i l, List.drop_eq_getElem_cons h]
  exact List.perm_middle.symm

theorem shuffle_go_perm {α γ : Type} [RandomGen γ] :
    ∀ (xs acc : List α) (g : γ), (shuffle.go xs acc g).1.Perm (xs ++ acc)
  | [], acc, g => by simp [shuffle.go]
  | x :: xs, acc, g => by
    rw [shuffle.go]
    dsimp only
    have hi : (randNat g 0 xs.length).1 % (x :: xs).length < (x :: xs).length :=
      Nat.mod_lt _ (Nat.succ_pos _)
    refine (shuffle_go_perm _ _ _).trans ?_
    refine List.perm_middle.trans ?_
    exact (getElem_cons_eraseIdx_perm _ _ hi).append_right acc
termination_by xs => xs.length
decreasing_by simp [List.length_eraseIdx, Nat.mod_lt _ (Nat.succ_pos xs.length)]

/-- Shuffling returns the same cards, in some order. -/
theorem shuffle_perm {α γ : Type} [RandomGen γ] (xs : List α) (g : γ) : (shuffle xs g).1.Perm xs := by
  unfold shuffle
  simpa using shuffle_go_perm xs [] g

/-! ## Drill -/

namespace Drill

variable {κ : Type} [DecidableEq κ]

/-- The invariant of a drill. -/
structure Inv (d : Drill κ) : Prop where
  /-- Correct answers plus remaining appearances: three per appearance in the session. -/
  count : ∀ c, d.passed.count c + d.pending.count c = passes * d.cards.count c
  /-- The queue holds only the session's cards. -/
  pending_sub : ∀ c ∈ d.pending, c ∈ d.cards
  /-- One rating per card. -/
  nodup : (d.firstRatings.map (·.1)).Nodup
  /-- Only the session's cards are rated. -/
  rated_sub : ∀ c ∈ d.firstRatings.map (·.1), c ∈ d.cards
  /-- A card answered correctly has been rated. -/
  passed_rated : ∀ c ∈ d.passed, (d.ratingOf? c).isSome

theorem ratingOf?_eq_none_iff (d : Drill κ) (c : κ) :
    d.ratingOf? c = none ↔ c ∉ d.firstRatings.map (·.1) := by
  simp only [ratingOf?, List.lookup_eq_none_iff, bne_iff_ne, ne_eq, List.mem_map, not_exists,
    not_and]
  exact ⟨fun h p hp hpc => h p hp hpc.symm, fun h p hp hpc => h p hp hpc.symm⟩

theorem inv_start (cards : List κ) : (start cards).Inv where
  count c := by simp [start, passes]; omega
  pending_sub c h := by simpa [start] using h
  nodup := by simp [start]
  rated_sub c h := by simp [start] at h
  passed_rated c h := by simp [start] at h

/-- The rating of a card that has one never changes. -/
theorem ratingOf?_answer_of_some {d : Drill κ} {c : κ} {r : Rating} (h : d.ratingOf? c = some r)
    (g : Grade) : (d.answer g).ratingOf? c = some r := by
  unfold answer
  split
  · exact h
  · simp only [ratingOf?] at h ⊢
    split <;> simp [List.lookup_append, h]

/-- The first answer to a card sets its rating to the grade's. -/
theorem ratingOf?_answer_first {d : Drill κ} {c : κ} (hc : d.current? = some c)
    (hf : d.isFirstAttempt c = true) (g : Grade) : (d.answer g).ratingOf? c = some g.rating := by
  unfold current? at hc
  unfold answer
  split
  · simp_all
  · rename_i c' rest hp
    simp only [hp, List.head?_cons, Option.some.injEq] at hc
    subst hc
    simp only [hf, ↓reduceIte, ratingOf?]
    have : d.firstRatings.lookup c' = none := by simpa [isFirstAttempt, ratingOf?] using hf
    simp [List.lookup_append, this]

theorem Inv.answer {d : Drill κ} (h : d.Inv) (g : Grade) : (d.answer g).Inv := by
  unfold Drill.answer
  split
  · exact h
  · rename_i c rest hp
    have hc : c ∈ d.cards := h.pending_sub c (by simp [hp])
    have hrated : ((d.answer g).ratingOf? c).isSome := by
      by_cases hf : d.isFirstAttempt c = true
      · rw [ratingOf?_answer_first (by simp [current?, hp]) hf]; rfl
      · have : (d.ratingOf? c).isSome := by
          simpa [isFirstAttempt, Option.isSome_iff_ne_none] using hf
        obtain ⟨r, hr⟩ := Option.isSome_iff_exists.1 this
        rw [ratingOf?_answer_of_some hr]; rfl
    unfold Drill.answer at hrated
    rw [hp] at hrated
    constructor
    · intro x
      have := h.count x
      rw [hp] at this
      split <;> simp_all [List.count_cons] <;> omega
    · intro x hx
      split at hx
      · simp only [List.mem_append, List.mem_singleton] at hx
        rcases hx with hx | rfl
        · exact h.pending_sub x (by simp [hp, hx])
        · exact hc
      · exact h.pending_sub x (by simp [hp, hx])
    · dsimp only
      split
      · rename_i hf
        have : c ∉ d.firstRatings.map (·.1) :=
          (ratingOf?_eq_none_iff d c).1 (by simpa [isFirstAttempt] using hf)
        have hn : ∀ (a : κ) (x : Rating), (a, x) ∈ d.firstRatings → ¬a = c :=
          fun a x hax hac => this (hac ▸ List.mem_map.2 ⟨(a, x), hax, rfl⟩)
        simpa [List.nodup_append] using ⟨h.nodup, hn⟩
      · exact h.nodup
    · intro x hx
      dsimp only at hx
      split at hx
      · simp only [List.map_append, List.map_cons, List.map_nil, List.mem_append,
          List.mem_singleton] at hx
        rcases hx with hx | rfl
        · exact h.rated_sub x hx
        · exact hc
      · exact h.rated_sub x hx
    · intro x hx
      dsimp only at hx
      split at hx
      · obtain ⟨r, hr⟩ := Option.isSome_iff_exists.1 (h.passed_rated x hx)
        have := ratingOf?_answer_of_some hr g
        unfold Drill.answer at this
        rw [hp] at this
        simp [this]
      · simp only [List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact hrated
        · obtain ⟨r, hr⟩ := Option.isSome_iff_exists.1 (h.passed_rated x hx)
          have := ratingOf?_answer_of_some hr g
          unfold Drill.answer at this
          rw [hp] at this
          simp [this]

/-- The invariant holds after any sequence of answers. -/
theorem inv_answers (cards : List κ) (gs : List Grade) :
    (gs.foldl Drill.answer (start cards)).Inv := by
  suffices ∀ d : Drill κ, d.Inv → (gs.foldl Drill.answer d).Inv from this _ (inv_start cards)
  induction gs with
  | nil => exact fun _ h => h
  | cons g gs ih => exact fun d h => ih _ (h.answer g)

/-- **A finished drill has had every card typed correctly three times.** -/
theorem Inv.passed_of_finished {d : Drill κ} (h : d.Inv) (hf : d.isFinished = true) (c : κ) :
    d.passed.count c = passes * d.cards.count c := by
  have := h.count c
  simp only [isFinished, List.isEmpty_iff] at hf
  simp_all

/-- **At the end of a drill every card of the session has been rated.** -/
theorem Inv.rated_of_finished {d : Drill κ} (h : d.Inv) (hf : d.isFinished = true) {c : κ}
    (hc : c ∈ d.cards) : (d.ratingOf? c).isSome := by
  have hcount := h.passed_of_finished hf c
  have : 0 < d.passed.count c := by
    have := List.count_pos_iff.2 hc
    simp only [passes] at hcount
    omega
  exact h.passed_rated c (List.count_pos_iff.1 this)

/-- Answers never add or remove cards from the session. -/
theorem cards_answer (d : Drill κ) (g : Grade) : (d.answer g).cards = d.cards := by
  unfold answer; split <;> rfl

/-- A correct (or nearly correct) answer shortens the queue by one; a wrong one requeues. -/
theorem pending_length_answer (d : Drill κ) (g : Grade) (hne : d.pending ≠ []) :
    (d.answer g).pending.length = if g = .wrong then d.pending.length else d.pending.length - 1 := by
  unfold answer
  split
  · contradiction
  · rename_i c rest hp
    rw [hp]
    split <;> simp

omit [DecidableEq κ] in
/-- The first pass asks each card once, in the shuffled order. -/
theorem start_pending (cards : List κ) : (start cards).pending = cards ++ cards ++ cards := rfl

end Drill

/-! ## Study -/

namespace Study

variable {κ : Type}

/-- A card that graduates leaves the session. -/
theorem answer_graduated {s : Study κ} {c : κ} {rest : List κ} (h : s.pending = c :: rest) :
    (s.answer true).pending = rest := by
  simp [answer, h]

/-- A card still in its learning steps is shown again, after all the others. -/
theorem answer_learning {s : Study κ} {c : κ} {rest : List κ} (h : s.pending = c :: rest) :
    (s.answer false).pending = rest ++ [c] := by
  simp [answer, h]

/-- A session never gains cards: what is pending after an answer was pending before. -/
theorem pending_answer_sub (s : Study κ) (b : Bool) : ∀ c ∈ (s.answer b).pending, c ∈ s.pending := by
  intro c hc
  unfold answer at hc
  split at hc
  · exact hc
  · rename_i c' rest hp
    rw [hp, List.mem_cons]
    split at hc
    · exact .inr hc
    · simp only [List.mem_append, List.mem_singleton] at hc
      exact hc.elim .inr .inl

end Study

end TurboAnki
