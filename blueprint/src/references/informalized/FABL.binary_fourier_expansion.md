<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter01/ProbabilityDensitiesAndConvolution.lean :: FABL.binary_fourier_expansion -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Binary Fourier expansion

**Claim.** Every function $f:\mathbb F_2^n\to\mathbb R$ satisfies $f(x)=\sum_{S\subseteq[n]}\widehat f(S)\chi_S(x)$, where the coefficients are its binary Fourier coefficients.

**Proof.** Expand $f$ in the Walsh basis: the basis representation identity expresses $f$ as the sum over subsets $S$ of its basis coefficient at $S$ times the corresponding Walsh character. Evaluating this identity at $x$ gives $f(x)=\sum_S ((\mathrm{binaryWalshBasis}\ n).\mathrm{repr}\ f\ S)\chi_S(x)$. The basis coefficient equals the binary Fourier coefficient by `binaryWalshBasis_repr_eq_binaryFourierCoeff`. Substituting this identity term by term yields the asserted expansion.

**Key facts.** `FABL.binaryWalshBasis_repr_eq_binaryFourierCoeff`.
