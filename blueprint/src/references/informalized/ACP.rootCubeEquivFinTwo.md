<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/RazborovSmolensky/LowDegreeObstruction.lean :: rootCubeEquivFinTwo -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# The root cube is the Boolean cube when `ω ≠ 1`

**Claim.** For a field `K`, `ω : K` with `hω : ω ≠ 1`, and any `n`, there is an equivalence
`rootCube ω n ≃ (Fin n → Fin 2)`, where `rootCube ω n = {x : Fin n → K // ∀ i, x i = 1 ∨ x i = ω}`.
The forward map records, coordinatewise, whether the value is `1` (bit `0`) or not (bit `1`);
the inverse sends bit `0` to `1` and bit `1` to `ω`.

**Proof.** The `Equiv` is assembled by `refine { toFun := …, invFun := …, left_inv := ?_, right_inv := ?_ }`.
- `toFun x i := if x.1 i = 1 then 0 else 1`; `invFun b := ⟨fun i => if b i = 0 then 1 else ω, _⟩`,
  whose membership side goal is `by_cases h : b i = 0 <;> simp [h]` (each coordinate is `1` or `ω`
  by construction).
- `left_inv`: after `Subtype.ext` and `funext i`, split on `x.1 i = 1`. In the `true` branch
  `simp [hx1]`. Otherwise `x.2 i` forces `x.1 i = ω`, and `ω ≠ 1` (used as `hωeq1`) makes the
  `if` take the second branch, so `simp [hxω, hωeq1]` closes it.
- `right_inv`: after `funext i`, split on `b i = 0`. If not, `b i = 1` since its value is
  `< 2` and `≠ 0` — proved by `Fin.ext` plus `omega` — and `simp [h1, hω]` finishes.

**Remark.** `hω : ω ≠ 1` is essential: for `ω = 1` the root cube is a singleton and no such
equivalence exists for `n ≥ 1`.

**Used in.** `rootCube_card_of_ne_one`, giving `Fintype.card (rootCube ω n) = 2 ^ n`.
