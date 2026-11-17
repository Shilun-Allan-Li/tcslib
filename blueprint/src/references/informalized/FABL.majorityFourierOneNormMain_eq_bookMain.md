<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/MajorityFourierOneNorm.lean :: FABL.majorityFourierOneNormMain_eq_bookMain -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Main-Term Expression for the One-Norm

**Claim.** For every nonnegative integer $m$, twice $2^m$ times the odd-majority influence main term equals $\frac{2}{\sqrt\pi}\frac{1}{\sqrt{2m+1}}2^{(2m+1)/2}$.

**Proof.** The exponent $(2m+1)/2$ is $m+1/2$, so its power of $2$ is $2^m\sqrt 2$. Also, the odd-majority influence main term is $\sqrt{2}/(\sqrt\pi\sqrt{2m+1})$, by separating the square root of the quotient into the square roots of its numerator and denominator. Substituting these two expressions into the left side gives $2\cdot2^m\cdot\sqrt{2}/(\sqrt\pi\sqrt{2m+1})$, which is the stated right side after rearranging factors.
