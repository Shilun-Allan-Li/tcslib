<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Switching.lean :: FABL.sum_restrictionAssignmentWeightAt_comp_freeCoordinateEmbedding -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Restriction Weight Under Coordinate Projection

**Claim.** The weighted sum over assignments on all coordinates of a function evaluated on the restrictions to $J$ equals the weighted sum of that function over assignments on $J$.

**Proof.** First sum out the coordinates outside $J$. The product weights on coordinates factor, and their total contribution is $1$, so the resulting sum is over assignments on $J$ alone (`FABL.sum_coordRestrictionProductWeight_restrict`). Identify the coordinates of $J$ with the indices $\{0,\ldots,|J|-1\}$ using the enumeration of $J$. Under this reindexing, the coordinate product weight is unchanged (`FABL.coordRestrictionProductWeight_reindex`), and the assignment on $J$ becomes an assignment on those indices. Thus the remaining sum is exactly the stated weighted sum over assignments to $|J|$ coordinates.

**Key facts.** `FABL.sum_coordRestrictionProductWeight_restrict`, `FABL.coordRestrictionProductWeight_reindex`.
