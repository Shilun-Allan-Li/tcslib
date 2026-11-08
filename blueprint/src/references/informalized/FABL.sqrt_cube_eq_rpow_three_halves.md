<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/NoiseStability/NoiseOperator.lean :: FABL.sqrt_cube_eq_rpow_three_halves -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Cube of a Square Root

**Claim.** For every $x\ge0$, $(\sqrt{x})^3=x^{3/2}$.

**Proof.** Since $(\sqrt{x})^2=x$, the left side is $x\sqrt{x}$. For nonnegative $x$, the square root equals $x^{1/2}$, while $x=x^1$. The product rule for real powers of a nonnegative base identifies $x^1x^{1/2}$ with $x^{1+1/2}=x^{3/2}$, including $x=0$.
