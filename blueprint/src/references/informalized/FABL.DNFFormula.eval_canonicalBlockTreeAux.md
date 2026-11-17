<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/HastadSwitching.lean :: FABL.DNFFormula.eval_canonicalBlockTreeAux -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation of the Canonical Block Tree

**Claim.** If the number of free coordinates under a restriction is at most the fuel, then for every input the canonical block tree constructed with that fuel evaluates to the formula's value on the corresponding completion.

**Proof.** Proceed by induction on the fuel, keeping the restriction arbitrary. If the fuel is zero, the bound forces there to be no free coordinates. Completions of a restriction with no free coordinates are independent of the input (`FABL.CoordRestriction.complete_eq_of_freeCoordinates_eq_empty`), so the tree's leaf value agrees with the formula at the completion specified by any input.

Now suppose the fuel is positive. If no term is compatible with the restriction, the formula evaluates to $1$ on every completion, which is exactly the tree's leaf value (`FABL.DNFFormula.eval_eq_one_of_no_compatible`). Otherwise, let $T$ be the canonical compatible term and let its free literal positions determine the coordinates queried by the tree.

If there are no such positions, $T$ is compatible and has no free literals. It therefore evaluates to $-1$ on every completion; since $T$ occurs in the formula, the formula also evaluates to $-1$. This matches the tree's leaf (`FABL.DNFTerm.eval_complete_eq_neg_one_of_compatible_of_no_free`, `FABL.DNFFormula.eval_eq_neg_one_iff`).

If there are free literal positions, the query block sends the input to the branch obtained by assigning those coordinates their input values. The query block evaluates through this assigned branch (`FABL.CoordinateDecisionTree.eval_queryCoordinates`), and fixing the block using that assignment agrees with fixing it using the original input (`FABL.CoordinateDecisionTree.fixCoordinateList_assignCoordinates`). The selected coordinates are distinct and free under the original restriction (`FABL.DNFTerm.coordinatesAtPositions_nodup`, `FABL.DNFTerm.coordinatesAt_freeLiteralPositions_all_free`); hence fixing them does not change the completion specified by the input (`FABL.CoordRestriction.complete_fixCoordinateList`).

At the resulting restriction, if $T$ remains compatible, its free literal positions are now empty (`FABL.DNFTerm.freeLiteralPositions_fixCoordinateList_eq_empty`). Thus $T$ evaluates to $-1$ on the input's completion, and the formula does too, so the branch's negative leaf is correct (`FABL.DNFTerm.eval_complete_eq_neg_one_of_compatible_of_no_free`, `FABL.DNFFormula.eval_eq_neg_one_iff`). If $T$ is not compatible there, the branch recurses with one less fuel. The queried coordinate list is nonempty (`FABL.DNFTerm.coordinatesAtPositions_nonempty_iff`), and all its coordinates were free; fixing the list therefore strictly reduces the number of free coordinates (`FABL.CoordRestriction.card_freeCoordinates_fixCoordinateList_lt`). The induction hypothesis applies to the recursive tree, and the unchanged completion identifies its output with the formula's value on the original input. This proves the claim in every case.

**Key facts.** `FABL.CoordRestriction.complete_eq_of_freeCoordinates_eq_empty`, `FABL.DNFFormula.eval_eq_one_of_no_compatible`, `FABL.DNFTerm.eval_complete_eq_neg_one_of_compatible_of_no_free`, `FABL.DNFFormula.eval_eq_neg_one_iff`, `FABL.CoordinateDecisionTree.eval_queryCoordinates`, `FABL.CoordinateDecisionTree.fixCoordinateList_assignCoordinates`, `FABL.DNFTerm.coordinatesAtPositions_nodup`, `FABL.DNFTerm.coordinatesAt_freeLiteralPositions_all_free`, `FABL.CoordRestriction.complete_fixCoordinateList`, `FABL.DNFTerm.freeLiteralPositions_fixCoordinateList_eq_empty`, `FABL.CoordRestriction.card_freeCoordinates_fixCoordinateList_lt`, `FABL.DNFTerm.coordinatesAtPositions_nonempty_iff`.
