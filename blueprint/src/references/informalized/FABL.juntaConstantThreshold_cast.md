<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/JuntaLearningReduction.lean :: FABL.juntaConstantThreshold_cast -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Real Form of the Testing Threshold

**Claim.** For every natural number $k$, the real number represented by the rational constant-testing threshold is $1-2/2^{k+2}$.

**Proof.** By definition, the threshold is $1$ minus twice the rational constant-testing accuracy. That accuracy is $1/2^{k+2}$. Casting this defining expression from the rationals to the reals preserves subtraction, multiplication, and the natural-number power of $2$, so the result is $1-2/2^{k+2}$ in $\mathbb R$.
