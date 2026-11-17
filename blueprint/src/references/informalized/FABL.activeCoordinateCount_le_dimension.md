<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/AC0ThresholdParitySeparation.lean :: FABL.activeCoordinateCount_le_dimension -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Active Coordinate Bound

**Claim.** For every natural number $m\ge 7$, $2m^2\le 2^m$.

**Proof.** The stated bound is precisely the auxiliary inequality that twice the square of $m$ is at most $2^m$; applying that inequality under the hypothesis $m\ge 7$ gives the result. Rewriting $2m^2$ as $m^2+m^2$ yields the displayed form.

**Key facts.** `FABL.two_mul_sq_le_two_pow_of_seven_le`.
