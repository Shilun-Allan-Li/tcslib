<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/General.lean :: holder_ineq_bool -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Hölder's inequality for Boolean functions

**Claim.** For `1 < p` and `f h : BooleanFunc n`,

`innerProduct f h ≤ (expect (fun x => |f x| ^ p)) ^ (1/p) *
                    (expect (fun x => |h x| ^ (p/(p-1)))) ^ ((p-1)/p)`,

i.e. `⟨f, h⟩ ≤ ‖f‖_p · ‖h‖_{p'}` for the uniform-measure norms, with
`p' = p/(p−1)` the conjugate exponent. Note the left side is the signed inner
product, not its absolute value.

**Proof.**

1. `unfold innerProduct`; the goal is about `uniformWeight n * ∑ x, f x * h x`.
2. Unweighted Hölder on the raw sums (`h_holder`): `Real.inner_le_Lp_mul_Lq`
   applied to `|f|` and `|h|` over `Finset.univ`, with the conjugacy hypothesis
   `Real.HolderConjugate p (p/(p-1))` discharged by
   `Real.holderConjugate_iff_eq_conjExponent hp`.
3. Sign step: `∑ x, f x * h x ≤ ∑ x, |f x| * |h x|` via `Finset.sum_le_sum` with
   `le_abs_self` and `abs_mul`, multiplied by `0 ≤ uniformWeight n` (`pow_nonneg`).
4. Constants: `unfold expect` and distribute `uniformWeight n` across the two
   `rpow` factors with `Real.mul_rpow`; the weight exponents recombine because
   `1/p + (p-1)/p = 1` (`Real.rpow_sub`, `mul_inv_cancel₀`, then `field_simp`).

**Used in.** The duality steps of both directions of the one-function ↔
two-function hypercontractivity equivalence, and in the low-norms interpolation
argument, always instantiated at the conjugate pair `(q, q/(q-1))`.
