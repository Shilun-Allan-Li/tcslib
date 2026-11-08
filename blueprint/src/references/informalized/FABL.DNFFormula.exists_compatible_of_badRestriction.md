<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Switching.lean :: FABL.DNFFormula.exists_compatible_of_badRestriction -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# A Compatible Term for a Nonconstant Restriction

**Claim.** If the restricted function is nonconstant, some term of the formula is compatible with the restriction.

**Proof.** Nonconstancy gives two inputs whose restricted values differ. Since the outputs are signs, at least one of those two values is $-1$: if both were $1$, they would agree. At an input where the formula evaluates to $-1$, the characterization of negative DNF evaluation supplies a term occurring in the formula that evaluates to $-1$ on that completion (`FABL.DNFFormula.eval_eq_neg_one_iff`). The chosen input therefore witnesses that term's compatibility, and its occurrence gives an index for it.

**Key facts.** `FABL.DNFFormula.eval_eq_neg_one_iff`.
