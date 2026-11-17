<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/MatchingMomentCombinatorics.lean :: FABL.graphMatchingEdgeAssignmentToLabeling_leftInverse -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Recovery of Edge Assignments

**Claim.** Converting an edge assignment to its induced vertex labeling and then recovering an edge assignment returns the original assignment.

**Proof.** The matching is unchanged by the conversion and recovery, so it remains to compare the labels on each edge. Fix a vertex $x$, let $e$ be the matching edge obtained from $x$, and let $r$ be the chosen representative of $e$. The representative property says that the matching edge obtained from $r$ is also $e$ (\texttt{FABL.graphMatchingEdgeRepresentative_spec}). Since these vertices yield the same matching edge, they are either the same vertex or adjacent in the matching (\texttt{FABL.matching_eq_or_adj_of_toEdge_eq}). In the first case their labels agree because they are the same vertex; in the second, they agree by compatibility of the given labeling across matching edges. Thus the recovered labeling agrees with the original at every vertex, proving recovery of the edge assignment.

**Key facts.** `FABL.graphMatchingEdgeRepresentative_spec`, `FABL.matching_eq_or_adj_of_toEdge_eq`.
