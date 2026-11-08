<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/TwoDivPi.lean :: FABL.integral_twoDivPiRademacherSummand_eq_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Mean of a Rademacher summand

**Claim.** For a uniformly chosen sign vector and any coordinate, the mean of the coordinate sign multiplied by its fixed coefficient is zero.

**Proof.** Factor the constant coefficient $a_i$ out of the integral. The remaining integral is the mean of the sign in coordinate $i$, which is zero by the fact that a Rademacher coordinate has mean zero (`integral_twoDivPiSignCoordinate_eq_zero`). Thus the original integral is $a_i\cdot 0=0$.

**Key facts.** `FABL.integral_twoDivPiSignCoordinate_eq_zero`.
