<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/BentDual.lean :: FABL.vectorFourierCoeff_vectorFourierCoeff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Double Fourier Transform

**Claim.** For every function $f:\mathbb{F}_2^n\to\mathbb{R}$ and every $x\in\mathbb{F}_2^n$, applying the Fourier transform twice gives $2^{-n}f(x)$.

**Proof.** Express the second Fourier transform as the average over indices $\gamma$ of the first Fourier coefficient times the Walsh character at $x$, using the expectation formula (`FABL.vectorFourierCoeff_eq_expect`). The Fourier expansion identity (`FABL.vector_fourier_expansion`) identifies the sum of these products with $f(x)$. The cube has $2^n$ elements, so its uniform average is $2^{-n}$ times this sum. Hence the result is $2^{-n}f(x)$. The character evaluations in the expansion agree by symmetry of the dot product.

**Key facts.** `FABL.vectorFourierCoeff_eq_expect`, `FABL.vector_fourier_expansion`.
