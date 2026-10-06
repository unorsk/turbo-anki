/-!
# Shuffling

Fisher–Yates by repeated extraction: pick a random remaining element, move it to the
result, repeat. Sessions are at most a few hundred cards, so the quadratic list
operations do not matter, and the result is easily seen (and proved, in
`TurboAnki.Proofs.Session`) to be a permutation of the input.
-/

namespace TurboAnki

/-- `xs` in random order, and the advanced generator. -/
def shuffle {α : Type} {γ : Type} [RandomGen γ] (xs : List α) (g : γ) : List α × γ :=
  go xs [] g
where
  go : List α → List α → γ → List α × γ
    | [], acc, g => (acc, g)
    | x :: xs, acc, g =>
      let rest := x :: xs
      let (r, g) := randNat g 0 xs.length
      let i := r % rest.length
      have : i < rest.length := Nat.mod_lt _ (Nat.succ_pos _)
      go (rest.eraseIdx i) (rest[i] :: acc) g
  termination_by xs => xs.length
  decreasing_by simp [List.length_eraseIdx, Nat.mod_lt _ (Nat.succ_pos xs.length)]

/-- Shuffles with a generator seeded from the clock. -/
def shuffleIO {α : Type} (xs : List α) : IO (List α) := do
  let seed ← IO.monoNanosNow
  return (shuffle xs (mkStdGen seed)).1

end TurboAnki
