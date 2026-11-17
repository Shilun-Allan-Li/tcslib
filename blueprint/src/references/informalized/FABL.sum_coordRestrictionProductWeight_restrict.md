<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Switching.lean :: FABL.sum_coordRestrictionProductWeight_restrict -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Restriction weights on selected coordinates

**Claim.** Summing over restriction assignments on all coordinates, with the product weights and a function that depends only on the assignments on $J$, equals the sum over assignments on $J$ alone with their product weights.

**Proof.** Split an assignment on the full coordinate set into its restriction to $J$ and its restriction to the complementary coordinates. This is a bijective reindexing of the finite sum. The product weight factors across these two coordinate sets (`FABL.coordRestrictionProductWeight_split`), and the function depends only on the assignment on $J$. For each fixed assignment on $J$, factor its weighted function value out of the sum over complementary assignments. The total weight of those complementary assignments is $1$ by the fact that all product weights on any finite coordinate set sum to one (`FABL.sum_coordRestrictionProductWeight`). The remaining sum is precisely the sum over assignments on $J$.

**Key facts.** `FABL.coordRestrictionProductWeight_split`, `FABL.sum_coordRestrictionProductWeight`.
