<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Pseudorandomness/ModThree.lean :: FABL.re_I_pow_eq_modFourPhase -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Real Part of an Even Power of the Imaginary Unit

**Claim.** For every even nonnegative integer $k$, the real part of $i^k$ is $(-1)^{\lfloor (k\bmod 4)/2\rfloor}$.

**Proof.** Write $k=2m$, using evenness. A direct division calculation gives $(2m\bmod 4)/2=m\bmod 2$. For a sign $-1$, raising it to an exponent depends only on that exponent modulo $2$, so the claimed right-hand side is $(-1)^m$. Meanwhile, $i^{2m}=(i^2)^m=(-1)^m$. The latter is real, and its real part is itself, proving the formula.
