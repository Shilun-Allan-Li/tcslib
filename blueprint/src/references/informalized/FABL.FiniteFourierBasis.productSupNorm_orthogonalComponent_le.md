<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/OrthogonalDecomposition.lean :: FABL.FiniteFourierBasis.productSupNorm_orthogonalComponent_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Supremum Bound for a Support Component

**Claim.** The supremum norm of the orthogonal component supported on $S$ is at most $2^{|S|}$ times the supremum norm of $f$.

**Proof.** For each point $x$ in the product space, the pointwise estimate (`abs_orthogonalComponent_le`) bounds the absolute value of the component by $2^{|S|}$ times the supremum norm of $f$. Taking the supremum over all such $x$ preserves this bound, yielding the asserted supremum-norm inequality.

**Key facts.** `FABL.FiniteFourierBasis.abs_orthogonalComponent_le`.
