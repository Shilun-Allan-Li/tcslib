<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/CNFReductions.lean :: FABL.length_le_three_of_mem_tseitinClauseChain -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Clause Width Bound

**Claim.** If the literal list has length at most the auxiliary list's length plus three, then every clause in the associated Tseitin clause chain has length at most three.

**Proof.** Use induction on the length of the literal list, following the recursive definition of the clause chain. When there are at least four literals and at least one auxiliary literal, the chain begins with a clause formed from the first two literals and that auxiliary literal, so this clause has length three. The remaining chain is formed after replacing the first two literals by the negation of the auxiliary literal and retaining the rest. The capacity inequality still holds for these shorter lists: removing three literals from the first list and one from the auxiliary list preserves the bound. The induction hypothesis bounds every clause in the remaining chain by three. If there are at least four literals but no auxiliary literals, the capacity inequality is impossible. In the terminal cases with at most three literals, the chain consists of the literal list itself, whose length is already at most three.
