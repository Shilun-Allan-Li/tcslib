<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Parity.lean :: FABL.parityBlockMinterm_eval_eq_neg_one_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Parity block minterm evaluation

**Claim.** The parity block minterm evaluates to $-1$ exactly when its assignment, normalized to $1$ at invalid block positions, agrees with the input block, which also uses $1$ at those positions.

**Proof.** A conjunction of literals evaluates to $-1$ exactly when every literal evaluates to $-1$, equivalently when every required coordinate sign matches the input (\(\texttt{DNFTerm.eval\_eq\_neg\_one\_iff}\)). Suppose first that the minterm evaluates to $-1$. For any valid position $j$ with $gr+j<n$, its corresponding literal occurs in the minterm, so the input sign at coordinate $gr+j$ equals the assigned sign there. At an invalid position, both the normalized assignment and the padded input block are $1$. These coordinatewise equalities give equality of the two block assignments. Conversely, suppose the normalized assignment equals the input block. Every literal in the minterm comes from a valid slot; at that slot the block equality says precisely that the input coordinate equals its required sign. Hence every literal evaluates to $-1$, so the conjunction does as well.

**Key facts.** `FABL.DNFTerm.eval_eq_neg_one_iff`.
