<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/MatchingMomentCombinatorics.lean :: FABL.isFourierHomogeneous_fourierDegree_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Degree Bound for a Homogeneous Fourier Spectrum

**Claim.** If every nonzero Fourier coefficient of a cube function is supported on a set of size exactly $k$, then its Fourier degree is at most $k$.

**Proof.** By `fourierDegree_le_iff`, it suffices to show that every frequency set whose size exceeds $k$ has zero Fourier coefficient. Suppose such a set $S$ had a nonzero coefficient. Fourier homogeneity would then force $|S|=k$, contradicting $k<|S|$. Therefore all coefficients at frequencies of size greater than $k$ vanish, and the degree is at most $k.

**Key facts.** `FABL.fourierDegree_le_iff`.
