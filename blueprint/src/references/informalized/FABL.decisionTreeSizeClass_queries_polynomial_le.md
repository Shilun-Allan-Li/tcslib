<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/KushilevitzMansour.lean :: FABL.decisionTreeSizeClass_queries_polynomial_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Decision tree query bound

**Claim.** If a real-output decision tree computes the real-valued sign representation of the target and has at most $s$ leaves, then every supported outcome of the specified learner has query count at most the displayed polynomial in $n$, $s$, and $1/\varepsilon$.

**Proof.** The Fourier $1$-norm of the target is at most the number of leaves of any decision tree computing it (`FABL.fourierOneNorm_le_leafCount_of_decisionTree`). Since the tree has at most $s$ leaves, the Fourier $1$-norm is therefore at most $s$. Its nonnegativity (`FABL.fourierOneNorm_nonneg`) supplies the required nonnegative norm bound. Apply the query-cost theorem for targets with bounded Fourier $1$-norm (`FABL.fourierOneNormClass_queries_polynomial_le`) with this norm bound. Its conclusion is exactly the stated query inequality.

**Key facts.** `FABL.fourierOneNorm_le_leafCount_of_decisionTree`, `FABL.fourierOneNorm_nonneg`, `FABL.fourierOneNormClass_queries_polynomial_le`.
