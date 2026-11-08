<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/KKL.lean :: FABL.fourier_ext -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Uniqueness from Fourier coefficients

**Claim.** If two real-valued functions on the Boolean cube have equal Fourier coefficients at every subset, then they are equal.

**Proof.** Fix an input $x$. By the Fourier expansion theorem, each function's value at $x$ is the sum, over all subsets $S$, of its Fourier coefficient at $S$ times the corresponding monomial. The assumed equality of coefficients makes the two summands equal for every $S$, hence their finite sums agree. Since this holds for every $x$, the functions are equal.

**Key facts.** `FABL.fourier_expansion`.
