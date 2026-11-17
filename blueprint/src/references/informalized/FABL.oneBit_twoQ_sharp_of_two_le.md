<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/NoiseOperatorExercises.lean :: FABL.oneBit_twoQ_sharp_of_two_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Sharp one-bit bound for exponents at least two

**Claim.** For $q\ge2$, the $q$-norm of $a+(q-1)^{-1/2}bx$ on a uniform sign is at most $\sqrt{a^2+b^2}$.

**Proof.** Split into the endpoint $q=2$ and the strict case $q>2$. At $q=2$, the affine-sign formula for the $2$-norm (\texttt{uniformLpNorm\_two\_affineSign}) identifies the left side with $\sqrt{a^2+b^2}$, since the noise factor is $1$. If $q>2$, the sharp one-bit $(2,q)$ inequality (\texttt{oneBit\_twoQ\_sharp}) bounds the left side by the $2$-norm of $a+bx$. The same affine-sign formula identifies that norm with $\sqrt{a^2+b^2}$, completing the proof.

**Key facts.** `FABL.oneBit_twoQ_sharp`, `FABL.uniformLpNorm_two_affineSign`.
