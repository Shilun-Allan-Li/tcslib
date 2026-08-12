<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Basic.lean :: fourierCoeff_empty -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# The empty Fourier coefficient is the mean

**Claim.** For every `f : BooleanFunc n`, `fourierCoeff f ∅ = expect f`: the
degree-zero Fourier coefficient `f̂(∅)` is just the average of `f`.

**Proof.** A single `simp [fourierCoeff, innerProduct, chiS, expect,
uniformWeight]`. Unfolding `chiS ∅` gives the empty product, which
`Finset.prod_empty` sends to `1`; so `f̂(∅) = ⟪f, χ_∅⟫ = 𝔼[f · 1] = 𝔼[f]` and
`mul_one` finishes. No induction or reindexing is involved — `∅` is the one
frequency whose character is constant.

**Remark.** Read contrapositively this is the standard balancedness criterion:
`f̂(∅) = 0` says exactly that `f` has mean zero. That is how it is used — at
`KKL.lean:590` and `KKL.lean:801` the empty-set case of a level decomposition is
discharged by `simp [hS, fourierCoeff_empty, hbal]`, where `hbal` is the
balancedness hypothesis.

**Used in.** `KKL.lean` (lines 590 and 801), to kill the `S = ∅` branch of
Fourier-level case splits for balanced functions.
