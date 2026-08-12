<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/KKL.lean :: noisyTotalInfluence -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# Noisy total influence

**Definition.** For a noise rate `ρ : ℝ` and `f : BooleanFunc n`,

`noisyTotalInfluence ρ f = ∑ S, S.card * ρ ^ (2 * S.card) * fourierCoeff f S ^ 2`.

This is the total influence with each Fourier level `|S|` damped by `ρ^(2|S|)`, the
quantity the KKL argument optimises over `ρ`. A plain definition; no proof.

**Remark.** Note the exponent is `2 * S.card`, not the `S.card - 1` used by
`noisyInfluence`; the two are related by
`noisyTotalInfluence ρ f ≤ ∑ i, noisyInfluence (ρ^2) i f`, which is Step B of
`KKL_balanced`.

**Status.** Dead declaration: nothing in the repository references
`noisyTotalInfluence`. Step B of `KKL_balanced` — its intended consumer — writes
the sum `∑ S, S.card * ρ^(2*S.card) * f̂(S)²` out by hand rather than naming it.
The `KKL_balanced` case that would use the definition in earnest is a `sorry`
(the hard case, needing log-convexity of `noisyInfluence`).
