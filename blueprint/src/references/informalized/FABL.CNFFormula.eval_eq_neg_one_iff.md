<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/CNFReductions.lean :: FABL.CNFFormula.eval_eq_neg_one_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Characterizing a negative formula value

**Claim.** A CNF formula evaluates to $-1$ at an assignment exactly when every clause evaluates to $-1$ there.

**Proof.** By definition, the formula evaluates to $-1$ precisely when every clause in its clause list has evaluation $-1$. Expressing membership in that list explicitly gives the stated condition, including the case of an empty list, where both universal conditions hold.
