<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/HastadSwitching.lean :: FABL.CoordRestriction.complete_fixCoordinate_signEncode -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Completion after fixing to the encoded sign

**Claim.** If coordinate $i$ is free, fixing it to the sign encoded by $x_i$ and then completing with $x$ gives the same vector as completing the original restriction with $x$.

**Proof.** The general fact that fixing a coordinate to its value in the original completion preserves the whole completion (`complete_fixCoordinate_eq_of_value`) applies here. At coordinate $i$, freeness means the original completion takes the value encoded by $x_i$, which is exactly the sign to which the coordinate is fixed. This supplies the required value hypothesis, and the stated equality follows.

**Key facts.** `FABL.CoordRestriction.complete_fixCoordinate_eq_of_value`.
