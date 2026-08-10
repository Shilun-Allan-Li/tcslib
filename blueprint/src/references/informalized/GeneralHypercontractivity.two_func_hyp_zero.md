<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/General.lean :: two_func_hyp_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Two-function hypercontractivity in dimension zero

**Claim.** For `p, q ≥ 1`, any `ρ : ℝ`, and `f g : BooleanFunc 0`,
`innerProduct f (noiseOp ρ g) ≤ (expect (fun x => |f x| ^ p)) ^ (1/p) * (expect (fun x => |g x| ^ q)) ^ (1/q)`.
The base case of the induction on the number of bits; no constraint on `ρ` is needed.

**Proof.** Four steps, after unfolding `innerProduct`, `expect` and `uniformWeight`.

1. `have h_noiseOp : ∀ x, noiseOp ρ g x = g x` — on `Fin 0` the only subset is `∅`
   (`Finset.univ = {∅}` by `decide`, then `Finset.sum_singleton`), and `chiS ∅ = 1`,
   so `noiseOp ρ g x = fourierCoeff g ∅ = g x` up to `Subsingleton.elim` on the
   one-point cube.
2. `BoolCube 0` is a singleton (`∀ x : Fin 0 → Bool, x = fun _ => true`, by `Fin.elim0`),
   so both sides collapse to the single point and the weight `2⁻⁰ = 1`
   (`simp_all +decide`).
3. The exponents cancel: `← Real.rpow_mul` with `mul_inv_cancel₀` and `Real.rpow_one`
   turn `(|f x| ^ p) ^ (1/p)` into `|f x|`, likewise for `g`.
4. What remains is `f x * g x ≤ |f x| * |g x|`, closed by `cases abs_cases … <;> nlinarith`. ∎

**Used in.** The `zero` branch of `hypercontractivity_induction`.
