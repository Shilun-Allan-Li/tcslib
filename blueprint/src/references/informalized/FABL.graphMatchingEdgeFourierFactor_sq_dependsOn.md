<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/MatchingMomentCombinatorics.lean :: FABL.graphMatchingEdgeFourierFactor_sq_dependsOn -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Dependence of the Squared Fourier Factor

**Claim.** The square of the Fourier factor for a fixed part is unchanged when two edge assignments agree on all matching edges incident to that part.

**Proof.** Agreement on the incident edges makes the unsquared Fourier factors equal, by the dependence property (\texttt{FABL.graphMatchingEdgeFourierFactor_dependsOn}). Applying the function $t\mapsto t^2$ to both sides gives equality of their squares.

**Key facts.** `FABL.graphMatchingEdgeFourierFactor_dependsOn`.
