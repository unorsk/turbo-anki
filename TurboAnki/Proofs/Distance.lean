import TurboAnki.Core.Distance

/-!
# Edit distance: theorems

The distance the drill uses to tell a typo from a mistake is a metric-like measure
with the expected properties:

* it is zero exactly between equal texts;
* it is symmetric — mistyping `a` for `b` is as far off as `b` for `a`;
* it is at most the length of the longer text, and at least the difference in length,
  so a near miss can never be much shorter or longer than the answer.

That the fast version computes the same function is `osaFast_eq` (with the
specification), in `TurboAnki.Core.Distance`.
-/

namespace TurboAnki.Distance

theorem cost_comm (x y : Char) : cost x y = cost y x := by
  unfold cost
  by_cases h : x = y <;> simp [h, eq_comm]

theorem cost_self (x : Char) : cost x x = 0 := by simp [cost]

theorem cost_eq_zero {x y : Char} (h : cost x y = 0) : x = y := by
  unfold cost at h
  split at h <;> simp_all

theorem cost_le_one (x y : Char) : cost x y ≤ 1 := by
  unfold cost; split <;> omega

theorem combine_le_sub (d i s : Nat) (w : Option Nat) : combine d i s w ≤ s := by
  unfold combine; split <;> omega

theorem le_combine {m d i s : Nat} {w : Option Nat} (hd : m ≤ d) (hi : m ≤ i) (hs : m ≤ s)
    (hw : ∀ t, w = some t → m ≤ t) : m ≤ combine d i s w := by
  unfold combine
  split
  · have := hw _ rfl; omega
  · omega

/-- Swap candidates cost at least one edit. -/
theorem swapOf_pos {x y : Char} {a b : List Char} {t : Nat} (h : swapOf x y a b = some t) : 1 ≤ t := by
  unfold swapOf at h
  split at h
  · split at h
    · simp only [Option.some.injEq] at h; omega
    · simp at h
  · simp at h

/-- A text is at distance zero from itself. -/
theorem osa_self : ∀ a : List Char, osa a a = 0
  | [] => osa_nil_left []
  | x :: a => by
    have := combine_le_sub (osa a (x :: a) + 1) (osa (x :: a) a + 1) (osa a a + cost x x)
      (swapOf x x a a)
    rw [osa_cons_cons]
    simp only [osa_self a, cost_self] at this ⊢
    omega

/-- Distance zero means equal texts: any edit at all costs something. -/
theorem eq_of_osa_eq_zero : ∀ {a b : List Char}, osa a b = 0 → a = b
  | [], b, h => by rw [osa_nil_left] at h; exact (List.length_eq_zero_iff.1 h).symm
  | x :: a, [], h => by rw [osa_nil_right] at h; simp at h
  | x :: a, y :: b, h => by
    rw [osa_cons_cons] at h
    have hlow : 1 ≤ combine (osa a (y :: b) + 1) (osa (x :: a) b + 1) (osa a b + cost x y)
        (swapOf x y a b) ∨ osa a b + cost x y = 0 := by
      by_cases hs : osa a b + cost x y = 0
      · exact .inr hs
      · exact .inl (le_combine (by omega) (by omega) (by omega) fun _ ht => swapOf_pos ht)
    rcases hlow with hlow | hs
    · omega
    · have hc : cost x y = 0 := by omega
      have ho : osa a b = 0 := by omega
      rw [cost_eq_zero hc, eq_of_osa_eq_zero ho]

theorem osa_eq_zero_iff {a b : List Char} : osa a b = 0 ↔ a = b :=
  ⟨eq_of_osa_eq_zero, fun h => h ▸ osa_self a⟩

theorem swapOf_comm (x y : Char) (a b : List Char)
    (ih : ∀ a' b', a'.length < a.length → b'.length < b.length → osa a' b' = osa b' a') :
    swapOf x y a b = swapOf y x b a := by
  cases a with
  | nil => cases b <;> rfl
  | cons x' a' =>
    cases b with
    | nil => rfl
    | cons y' b' =>
      have h := ih a' b' (by simp) (by simp)
      simp only [swapOf]
      by_cases hc : x = y' ∧ x' = y
      · have hc' : y = x' ∧ y' = x := ⟨hc.2.symm, hc.1.symm⟩
        rw [ite_eq_left_of_eq_true _ _ (eq_true hc), ite_eq_left_of_eq_true _ _ (eq_true hc'), h]
      · have hc' : ¬(y = x' ∧ y' = x) := fun h' => hc ⟨h'.2.symm, h'.1.symm⟩
        rw [ite_eq_right_of_eq_false _ _ (eq_false hc), ite_eq_right_of_eq_false _ _ (eq_false hc')]

/-- The distance is symmetric. -/
theorem osa_comm : ∀ a b : List Char, osa a b = osa b a
  | [], b => by rw [osa_nil_left, osa_nil_right]
  | x :: a, [] => by rw [osa_nil_left, osa_nil_right]
  | x :: a, y :: b => by
    have h1 := osa_comm a (y :: b)
    have h2 := osa_comm (x :: a) b
    have h3 := osa_comm a b
    have hs := swapOf_comm x y a b fun a' b' _ _ => osa_comm a' b'
    rw [osa_cons_cons, osa_cons_cons, h1, h2, h3, hs, cost_comm x y]
    unfold combine
    split <;> omega
termination_by a b => a.length + b.length

/-- The distance is at most the length of the longer text (substitute, then insert or
delete the rest). -/
theorem osa_le_max_length : ∀ a b : List Char, osa a b ≤ max a.length b.length
  | [], b => by rw [osa_nil_left]; omega
  | x :: a, [] => by rw [osa_nil_right]; simp
  | x :: a, y :: b => by
    have := osa_le_max_length a b
    have := combine_le_sub (osa a (y :: b) + 1) (osa (x :: a) b + 1) (osa a b + cost x y)
      (swapOf x y a b)
    have := cost_le_one x y
    rw [osa_cons_cons]
    simp only [List.length_cons]
    omega

/-- The distance is at least the difference in length: every edit changes the length
by at most one. -/
theorem length_sub_le_osa : ∀ a b : List Char,
    a.length - b.length ≤ osa a b ∧ b.length - a.length ≤ osa a b
  | [], b => by simp [osa_nil_left]
  | x :: a, [] => by simp [osa_nil_right]
  | x :: a, y :: b => by
    have h1 := length_sub_le_osa a (y :: b)
    have h2 := length_sub_le_osa (x :: a) b
    have h3 := length_sub_le_osa a b
    have hw : ∀ t, swapOf x y a b = some t →
        (x :: a).length - (y :: b).length ≤ t ∧ (y :: b).length - (x :: a).length ≤ t := by
      intro t ht
      cases a with
      | nil => simp [swapOf] at ht
      | cons x' a' =>
        cases b with
        | nil => simp [swapOf] at ht
        | cons y' b' =>
          have h4 := length_sub_le_osa a' b'
          simp only [swapOf] at ht
          split at ht
          · simp only [Option.some.injEq] at ht
            subst ht
            simp only [List.length_cons] at *
            omega
          · simp at ht
    simp only [List.length_cons] at h1 h2 h3 hw ⊢
    rw [osa_cons_cons]
    exact ⟨le_combine (by omega) (by omega) (by omega) fun t ht => (hw t ht).1,
           le_combine (by omega) (by omega) (by omega) fun t ht => (hw t ht).2⟩
termination_by a b => a.length + b.length

end TurboAnki.Distance
