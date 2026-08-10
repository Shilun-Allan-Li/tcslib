<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/General.lean :: low_norms_interpolation_params -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Existence of interpolation parameters in the low-norms range

**Claim.** (`private`.) Let `1 < p < u < 2` and `ρ ^ 2 = (p - 1) / (u - 1)`.
Then there exist `θ s : ℝ` with `0 < θ`, `θ < 1`, `0 < s` and

`1/p = θ/(1 + ρ^2) + (1 - θ)/s`  and  `1/u = θ/2 + (1 - θ)/s`.

Purely an algebraic bookkeeping lemma: it asserts that the two Riesz–Thorin
interpolation constraints can be met simultaneously in this parameter range.

**Proof.** Explicit witnesses, `θ = 2(u + p - 2)/(p * u)` and `s = 2 - p`,
supplied by `refine' ⟨_, _, _, _, _, _, _⟩` with `nlinarith` on the easy goals.

1. `0 < θ`: `div_pos`, using `p + u > 2` (from `1 < p < u`) and `p * u > 0`.
2. `θ < 1`: `div_lt_iff₀` then `nlinarith`.
3. `0 < s`: `2 - p > 0` from `p < u < 2`.
4. The two equations: `grind +splitIndPred` and `grind` — after substituting
   `ρ^2 = (p-1)/(u-1)` both reduce to rational identities in `p, u`.

**Note.** As written this lemma has no consumers anywhere in the repository
(see report).
