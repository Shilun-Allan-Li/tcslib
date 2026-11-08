<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/ExactSparseSpectrumLearning.lean :: FABL.exactSparseSpectrumGoldreichLevinInput_runtimeScale_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Runtime Scale Bound

**Claim.** For natural numbers $n$ and $k$ with $n>0$, the runtime scale of the exact sparse-spectrum Goldreich–Levin input is at most $12(n+1)(2^k+1)^2$.

**Proof.** Write $X=2^k$, regarded as a positive real number. The input's Fourier bound is $2^{k+1}=2X$, so the numerator in its runtime scale contains the factor $2X+1$. Its learning parameter, after casting to the reals, is the encoded accuracy (`DeterministicGoldreichLevinInput.learningParameter_cast`), namely $1/(4X)$. Thus the runtime scale is $4(n+1)(2X+1)X$. For $X>0$, the inequality $(2X+1)X\leq 3(X+1)^2$ follows by expanding both sides: their difference is $X^2+5X+3$, which is nonnegative. Multiplying by the nonnegative factor $4(n+1)$ gives a bound of $12(n+1)(X+1)^2$. Substituting $X=2^k$ yields the stated result.

**Key facts.** `FABL.DeterministicGoldreichLevinInput.learningParameter_cast`.
