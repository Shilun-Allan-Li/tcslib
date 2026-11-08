<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/VectorValuedFourier.lean :: FABL.FiniteFourierBasis.vector_fourier_expansion -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Vector-Valued Fourier Expansion

**Claim.** For every point $x$, a vector-valued function $f(x)$ equals the sum of its product basis functions at $x$, each multiplied by the corresponding vector Fourier coefficient.

**Proof.** Fix $x$ and let $d$ be the difference between $f(x)$ and the proposed Fourier sum. Apply the scalar Fourier expansion (`fourier_expansion`) to the real-valued function $y\mapsto\langle d,f(y)\rangle$. Its value at $x$ is the sum of its scalar Fourier coefficients multiplied by the product basis functions at $x$. The inner product of $d$ with the proposed vector sum is the same sum: the identity relating the inner product with a vector Fourier coefficient to the scalar Fourier coefficient (`real_inner_vectorFourierCoeff`) identifies each term. Hence $\langle d,d\rangle=0$. Positive definiteness of the inner product gives $d=0$, which is the claimed expansion.

**Key facts.** `FABL.FiniteFourierBasis.fourier_expansion`, `FABL.FiniteFourierBasis.real_inner_vectorFourierCoeff`.
