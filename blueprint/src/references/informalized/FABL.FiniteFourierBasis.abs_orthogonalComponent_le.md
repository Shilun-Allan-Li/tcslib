<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/OrthogonalDecomposition.lean :: FABL.FiniteFourierBasis.abs_orthogonalComponent_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bound on an Orthogonal Fourier Component

**Claim.** The absolute value of the Fourier component supported on $S$ is at most $2^{|S|}$ times the supremum norm of $f$.

**Proof.** Rewrite the orthogonal component using its Möbius expansion (`orthogonalComponent_eq_mobius`): it is a sum over subsets $J\subseteq S$, with coefficient $(-1)^{|S|-|J|}$ multiplying the projection onto coordinates in $J$. The triangle inequality bounds its absolute value by the sum of the absolute values of these terms. Each coefficient has absolute value one, and each projection is bounded in absolute value by the supremum norm of $f$ (`abs_projectOnCoordinates_le_productSupNorm`). There are $2^{|S|}$ subsets of $S$, so the sum is at most $2^{|S|}$ times that norm.

**Key facts.** `FABL.FiniteFourierBasis.orthogonalComponent_eq_mobius`, `FABL.abs_projectOnCoordinates_le_productSupNorm`.
