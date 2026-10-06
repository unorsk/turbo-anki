/-!
# Edit distance

Optimal string alignment distance: the Levenshtein distance plus the swap of two
adjacent characters as a single edit, because typing `hnud` for `hund` is one slip of
the fingers, not two. This is the distance melk's drill uses to tell typos from
mistakes.

`osa` is the specification, a direct recursion over both texts. It takes exponential
time, so `osaFast` computes the same function row by row in `a.length * b.length`
steps and replaces it in compiled code (`@[csimp]` in `TurboAnki.Proofs.Distance`,
where its properties are proved).
-/

namespace TurboAnki.Distance

/-- The cost of aligning two characters. -/
def cost (x y : Char) : Nat := if x = y then 0 else 1

/-- The best of deleting, inserting, substituting and (where possible) swapping. -/
def combine (del ins sub : Nat) (swap : Option Nat) : Nat :=
  match swap with
  | some t => min (min (min del ins) sub) t
  | none => min (min del ins) sub

/-- The distance between `a` and `b` (the specification). -/
def osa : List Char → List Char → Nat
  | [], b => b.length
  | a, [] => a.length
  | x :: a, y :: b =>
    combine (osa a (y :: b) + 1) (osa (x :: a) b + 1) (osa a b + cost x y)
      (match ha : a, hb : b with
        | x' :: a', y' :: b' => if x = y' ∧ x' = y then some (osa a' b' + 1) else none
        | _, _ => none)
termination_by a b => a.length + b.length
decreasing_by all_goals (subst_vars; simp only [List.length_cons]; omega)

/-! ## Row by row -/

/-- The distances from `a` to `b` and to each suffix of `b`, longest first (the row of
the table for `a`). What the functions below compute. -/
def specRow (a : List Char) : List Char → List Nat
  | [] => [osa a []]
  | y :: b => osa a (y :: b) :: specRow a b

/-- The row of the empty text. -/
def rowNil : List Char → List Nat
  | [] => [0]
  | _ :: b => (b.length + 1) :: rowNil b

/-- The row of `x :: a` from the row `r1` of `a` and the row `r2` of `a.tail`. The row is
built from the right, so the entry for the next suffix of `b` is at hand. -/
def rowCons (x : Char) (a : List Char) : List Nat → List Nat → List Char → List Nat
  | _, _, [] => [a.length + 1]
  | r1, r2, y :: b =>
    let rest := rowCons x a r1.tail r2.tail b
    let swap := match a, b with
      | x' :: _, y' :: _ => if x = y' ∧ x' = y then some (r2.tail.tail.headD 0 + 1) else none
      | _, _ => none
    combine (r1.headD 0 + 1) (rest.headD 0 + 1) (r1.tail.headD 0 + cost x y) swap :: rest

/-- The rows of `a` and of `a.tail`, against `b`. -/
def rows (b : List Char) : List Char → List Nat × List Nat
  | [] => (rowNil b, rowNil b)
  | x :: a =>
    let (r1, r2) := rows b a
    (rowCons x a r1 r2 b, r1)

/-- The distance between `a` and `b`, by dynamic programming. -/
def osaFast (a b : List Char) : Nat := (rows b a).1.headD 0

/-! ## The two agree -/

/-- The swap candidate of `osa (x :: a) (y :: b)`. -/
def swapOf (x y : Char) (a b : List Char) : Option Nat :=
  match a, b with
  | x' :: a', y' :: b' => if x = y' ∧ x' = y then some (osa a' b' + 1) else none
  | _, _ => none


theorem osa_nil_left (b : List Char) : osa [] b = b.length := by
  simp [osa]

theorem osa_nil_right (a : List Char) : osa a [] = a.length := by
  cases a <;> simp [osa]

theorem osa_cons_cons (x y : Char) (a b : List Char) :
    osa (x :: a) (y :: b) =
      combine (osa a (y :: b) + 1) (osa (x :: a) b + 1) (osa a b + cost x y) (swapOf x y a b) := by
  conv => lhs; unfold osa
  cases a <;> cases b <;> rfl

theorem specRow_headD (a b : List Char) : (specRow a b).headD 0 = osa a b := by
  cases b <;> rfl

theorem specRow_head? (a b : List Char) : (specRow a b).head? = some (osa a b) := by
  cases b <;> rfl

theorem rowNil_eq (b : List Char) : rowNil b = specRow [] b := by
  induction b with
  | nil => simp [rowNil, specRow, osa_nil_left]
  | cons y b ih => simp [rowNil, specRow, osa_nil_left, ih]

theorem rowCons_eq (x : Char) (a : List Char) :
    ∀ (b : List Char) (r2 : List Nat), (∀ x' a', a = x' :: a' → r2 = specRow a' b) →
      rowCons x a (specRow a b) r2 b = specRow (x :: a) b := by
  intro b
  induction b with
  | nil => intro _ _; simp [rowCons, specRow, osa_nil_right]
  | cons y b ih =>
    intro r2 h2
    have hrest : rowCons x a (specRow a b) r2.tail b = specRow (x :: a) b :=
      ih r2.tail fun x' a' ha => by rw [h2 x' a' ha]; rfl
    simp only [rowCons, specRow, List.tail_cons, hrest, osa_cons_cons, List.headD_cons, specRow_headD]
    cases a with
    | nil => rfl
    | cons x' a' =>
      cases b with
      | nil => rfl
      | cons y' b' => simp [swapOf, h2 _ _ rfl, specRow, specRow_head?]

theorem rows_eq (b : List Char) :
    ∀ a : List Char, (rows b a).1 = specRow a b ∧ ∀ x' a', a = x' :: a' → (rows b a).2 = specRow a' b
  | [] => ⟨rowNil_eq b, fun _ _ h => nomatch h⟩
  | x :: a =>
    have ih := rows_eq b a
    ⟨by simp only [rows]; rw [ih.1]; exact rowCons_eq x a b _ ih.2,
     fun _ _ h => by cases h; simp only [rows]; exact ih.1⟩

theorem osaFast_eq (a b : List Char) : osaFast a b = osa a b := by
  rw [osaFast, (rows_eq b a).1, specRow_headD]

@[csimp] theorem osa_eq_osaFast : @osa = @osaFast := by
  funext a b
  exact (osaFast_eq a b).symm

end TurboAnki.Distance
