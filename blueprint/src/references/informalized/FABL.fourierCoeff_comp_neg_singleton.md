<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/GaussianSharpLevelOneCounterexample.lean :: FABL.fourierCoeff_comp_neg_singleton -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Singleton Coefficient Under Sign Reversal

**Claim.** For every natural number $n$, every real-valued function $f$ on the $n$-dimensional sign cube, and every coordinate $i$, the Fourier coefficient at $\{i\}$ of $x\mapsto f(-x)$ is the negative of the Fourier coefficient of $f$ at $\{i\}$.

**Proof.** Change variables in the defining expectation by the bijection $x\mapsto -x$. The coefficient becomes the expectation of $f(x)$ multiplied by the monomial at $-x$. The monomial sign-reversal identity gives a factor $(-1)^{|\{i\}|}=-1$ (`monomial_neg_input_counterexample`). Hence the integrand is the negative of the one defining the original coefficient, and linearity of expectation over negation yields the result.

**Key facts.** `FABL.monomial_neg_input_counterexample`.
