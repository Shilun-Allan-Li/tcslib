<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/MonotoneLargeCoefficient.lean :: FABL.exists_nonempty_singleton_fourierCoeff_sq_ge_edgeKKL_sq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# A Large Singleton Fourier Coefficient

**Claim.** For a nonconstant monotone Boolean function $f$, there is a nonempty set $S$ of size at most one whose squared Fourier coefficient is at least the square of the stated edge-KKL lower bound.

**Proof.** By the edge-KKL coefficient bound ( `exists_singletonCoeff_ge_edgeKKL`), there is a coordinate $i$ whose singleton Fourier coefficient is at least $9\,9^{-I[f]/\operatorname{Var}[f]}/(I[f]/\operatorname{Var}[f])^2$, with the notation for total influence and variance as in the statement. Take $S=\{i\}$, which is nonempty and has size one. The lower bound is nonnegative: its numerator is nonnegative because the real power of the positive number $9$ is positive, and its denominator is a square. Squaring the coefficient inequality therefore preserves its direction and gives the required conclusion.

**Key facts.** `FABL.exists_singletonCoeff_ge_edgeKKL`.
