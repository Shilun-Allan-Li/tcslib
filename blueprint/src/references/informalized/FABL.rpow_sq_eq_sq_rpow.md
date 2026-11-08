<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/NoiseOperatorExercises.lean :: FABL.rpow_sq_eq_sq_rpow -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Square of a real power

**Claim.** For every $x\ge 0$ and real $t$, $(x^t)^2=(x^2)^t$.

**Proof.** The square of $x^t$ is $x^{2t}$ by the natural-number power rule for real powers (`Real.rpow_mul_natCast`). Commutativity of multiplication identifies $t\cdot2$ with $2\cdot t$. The rule for moving a natural-number factor from the exponent to the base (`Real.rpow_natCast_mul`) then gives $(x^2)^t$.
