<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/MatchingMomentCombinatorics.lean :: FABL.graphMatchingEdgeFourierFactor_dependsOn -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Dependence on Incident Edges

**Claim.** The Fourier factor for a fixed part is unchanged when two edge assignments agree on all matching edges incident to that part.

**Proof.** The factor is the absolute value of the Fourier coefficient indexed by the set of labels assigned along the matching edges at the fixed part. For each position in that part, its matching edge belongs to the set of incident edges (\texttt{FABL.graphMatchingPartEdge_mem}); thus the two assignments give the same label at every such position. Their image sets of labels are therefore equal, so the Fourier coefficients, and hence their absolute values, agree.

**Key facts.** `FABL.graphMatchingPartEdge_mem`.
