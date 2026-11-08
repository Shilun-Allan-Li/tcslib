<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/SubspacesAndDecisionTrees/Subspaces.lean :: FABL.setIndicator_submodule_apply -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Subspace Indicator Formula

**Claim.** The indicator of a subspace $A$ at $x$ is $2^{-\operatorname{codim}(A)}$ times the sum of the characters indexed by vectors perpendicular to $A$, evaluated at $x$.

**Proof.** Split according to whether $x\in A$. If $x\in A$, then the double perpendicular is $A$ (`perpendicularSubspace_perpendicularSubspace`), so $x$ lies in the perpendicular of the character-summation subspace. The character sum over that subspace is consequently its cardinality (`subspaceCharacterSum_eq_card_of_mem`). That cardinality is $2^{\operatorname{codim}(A)}$ (`card_perpendicularSubspace`), and multiplication by its reciprocal gives $1$, the indicator value at $x$. If $x\notin A$, the double-perpendicular identity shows that $x$ is not in the perpendicular of the summation subspace. The character sum is then zero (`subspaceCharacterSum_eq_zero_of_not_mem`), matching the indicator. These cases prove the formula.

**Key facts.** `FABL.perpendicularSubspace_perpendicularSubspace`, `FABL.subspaceCharacterSum_eq_card_of_mem`, `FABL.card_perpendicularSubspace`, `FABL.subspaceCharacterSum_eq_zero_of_not_mem`.
