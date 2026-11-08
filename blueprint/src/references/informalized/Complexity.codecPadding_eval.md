<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/TQBF.lean :: Complexity.codecPadding_eval -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation of the Padding Encoding

**Claim.** The padding CNF encoding evaluates to true exactly when every assignment bit with index $j$ satisfying $\mathrm{first}\le j<L$ is false.

**Proof.** The encoding contains one negative unit clause for each index of the form $\mathrm{first}+i$ with $i<L-\mathrm{first}$. Such a clause is true exactly when the assignment at that index is false. Thus the whole conjunction is true precisely when the assignment is false at every index in this range. These indices are exactly those $j$ with $\mathrm{first}\le j<L$: write $j=\mathrm{first}+(j-\mathrm{first})$ in one direction, and use $\mathrm{first}+i<L$ in the other. If $L\le\mathrm{first}$, both the clause list and the stated index interval are empty, so the equivalence still holds.
