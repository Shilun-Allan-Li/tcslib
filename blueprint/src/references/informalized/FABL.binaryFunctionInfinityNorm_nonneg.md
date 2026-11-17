<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/SubspacesAndDecisionTrees/VectorFourier.lean :: FABL.binaryFunctionInfinityNorm_nonneg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Nonnegativity of the infinity norm

**Claim.** For every real-valued function $f$ on the binary cube, its infinity norm is nonnegative.

**Proof.** The infinity norm bounds $|f(x)|$ at every point $x$. In particular, it bounds $|f(0)|$, which is nonnegative. Therefore the infinity norm is nonnegative.

**Key facts.** `FABL.abs_le_binaryFunctionInfinityNorm`.
