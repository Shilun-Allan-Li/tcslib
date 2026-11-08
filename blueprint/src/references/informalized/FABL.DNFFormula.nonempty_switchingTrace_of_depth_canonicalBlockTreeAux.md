<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/HastadSwitching.lean :: FABL.DNFFormula.nonempty_switchingTrace_of_depth_canonicalBlockTreeAux -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Switching Trace from Auxiliary Tree Depth

**Claim.** If the canonical block decision tree built with fuel $m$ has depth at least $k+1$, then there exists a switching trace for the formula relative to the restriction with parameter $k+1$.

**Proof.** Proceed by induction on the fuel, generalizing the restriction and the target parameter. At fuel zero the tree is a leaf, so its depth cannot reach $k+1$; the depth hypothesis is impossible. For successor fuel, split according to whether there is a compatible term and, if so, whether its free-literal positions are nonempty. If there is no compatible term, or there are no free positions, the tree is a leaf, again contradicting the positive depth bound.

In the remaining case, let $T$ be the canonical compatible term, let $P$ be its free-literal positions, and let the tree query the coordinates belonging to those positions. If $|P|\ge k+1$, choose a subset of $P$ of size $k+1$. It directly supplies a final switching trace. Otherwise, the queried coordinate list has length $|P|<k+1$. The depth bound for the query tree then yields an assignment to the queried coordinates whose continuation has depth at least $k+1-|P|$ (by `exists_finish_depth_ge_sub_of_depth_queryCoordinates`). The term $T$ must be incompatible with the restriction after these coordinates are fixed: if it were compatible, that continuation would be a leaf and could not have the required positive depth. The continuation therefore comes from the recursive auxiliary tree. Apply the induction hypothesis to it with parameter $k-|P|$, which is valid because its required depth is at least $k+1-|P|$. Finally, prepend the current term and the assignment to the resulting trace: the number of free positions is $|P|$, the current term has become incompatible after fixing them, and the recursive trace supplies the remaining parameter. This constructs the desired trace.

**Key facts.** `FABL.CoordinateDecisionTree.exists_finish_depth_ge_sub_of_depth_queryCoordinates`.
