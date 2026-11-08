<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/MatchingMomentCombinatorics.lean :: FABL.not_mem_listSymmDiff_iff_even_countP -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Even Occurrence and Symmetric Difference

**Claim.** An element is absent from the symmetric difference of a finite list of finite sets exactly when it occurs in an even number of the listed sets.

**Proof.** Induct on the list. For the empty list, the symmetric difference is empty and the occurrence count is zero, so both conditions hold. For a list with first set $S$ and remaining list $R$, the element belongs to $S\triangle\operatorname{symmDiff}(R)$ exactly when its membership in $S$ differs from its membership in the symmetric difference of $R$. By the induction hypothesis, absence from the latter is equivalent to an even occurrence count in $R$. Adding the first set toggles the parity of the count exactly when $x\in S$; thus absence from the new symmetric difference is equivalent to the total count being even.
