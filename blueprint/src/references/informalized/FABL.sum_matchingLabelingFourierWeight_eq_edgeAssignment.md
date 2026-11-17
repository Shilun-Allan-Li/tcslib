<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/MatchingMomentCombinatorics.lean :: FABL.sum_matchingLabelingFourierWeight_eq_edgeAssignment -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: low -->

# Matching labeling and edge assignment sums

**Claim.** The sum of the matching-labeling Fourier weights equals the sum over perfect matchings and edge label assignments of the corresponding products of Fourier factors.

**Proof.** Use the bijection between compatible vertex labelings of a perfect matching and assignments of labels to its edges, and reindex the finite sum along this bijection. For each labeling, the weight of its corresponding edge assignment is exactly the product of the edge-assignment Fourier factors, by the weight identity for the assignment-to-labeling map (\(\texttt{FABL.graphMatchingEdgeAssignmentToLabeling_weight}\)). Hence the summands agree under the bijection, giving equality of the sums.

**Key facts.** `FABL.graphMatchingEdgeAssignmentToLabeling_weight`.

**Caveat.** The proof source invokes the equivalence \(\texttt{graphMatchingLabelingEquivEdgeAssignment}\), but it is not listed among the supplied upstream facts. The reindexing route is clear, but the bijection's construction is not available here.
