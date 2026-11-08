<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/HypercontractivityExercises.lean :: FABL.uniformLpNorm_two_degreeTruncation_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Degree Truncation Is Contractive in $L^2$

**Claim.** For $k\in\mathbb N$ and $f\colon\{-1,1\}^n\to\mathbb R$, the degree-at-most-$k$ truncation has uniform $2$-norm at most that of $f$.

**Proof.** Both norms are nonnegative (\texttt{uniformLpNorm_nonneg}), so it suffices to compare their squares. By the identity between the squared uniform $2$-norm and the uniform inner product (\texttt{uniformLpNorm_two_sq_eq_uniformInner}), followed by Parseval's identity (\texttt{parseval}), these squares are the sums of squared Fourier coefficients. The Fourier coefficients of the truncation equal those of $f$ on subsets of size at most $k$ and are zero on all other subsets (\texttt{fourierCoeff_degreeTruncation}). Hence each squared coefficient in the truncation's sum is at most the corresponding squared coefficient for $f$, and summing gives the squared-norm comparison. Taking square roots preserves the inequality.

**Key facts.** `FABL.uniformLpNorm_nonneg`, `FABL.uniformLpNorm_two_sq_eq_uniformInner`, `FABL.parseval`, `FABL.fourierCoeff_degreeTruncation`.

**Caveat.** The supplied informal statement describes bounds for general $q$, but the formal statement and proof establish only the $q=2$ contraction result stated here.
