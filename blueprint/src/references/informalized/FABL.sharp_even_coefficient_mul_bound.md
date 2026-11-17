<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/HypercontractiveMomentSharpness.lean :: FABL.sharp_even_coefficient_mul_bound -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Sharp even coefficient identity

**Claim.** For $0<r$ and $l\le r$, the product of the even binomial coefficient, the noise parameter to power $2l$, and the sharp even moment bound equals $\binom rl$.

**Proof.** Square the noise parameter first: its square is $1/(2r-1)$ (`sharpEvenMomentNoise_sq`). Consequently its $2l$-th power is $(2r-1)^{-l}$. Substituting the definition of the sharp even moment bound, the left side becomes $\binom{2r}{2l}(2r-1)^l\binom rl/\binom{2r}{2l}\cdot(2r-1)^{-l}$. The positive hypotheses ensure the denominators are nonzero, and cancellation leaves $\binom rl$.

**Key facts.** `FABL.sharpEvenMomentNoise_sq`.
