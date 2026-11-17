<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/HastadSwitching.lean :: FABL.DNFFormula.eval_eq_one_of_no_compatible -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation with No Compatible Term

**Claim.** If no term is compatible with a restriction, then the formula evaluates to $1$ on every completion of that restriction.

**Proof.** Fix an input and consider the formula's value on its completion. A sign-valued output is either $1$ or $-1$. If it is $1$, the conclusion follows. If it is $-1$, the characterization of negative DNF evaluation yields a term occurring in the formula that evaluates to $-1$ at this completion (`FABL.DNFFormula.eval_eq_neg_one_iff`). That very input witnesses the term's compatibility, contradicting the assumption that there are no compatible term indices. Thus the value must be $1$.

**Key facts.** `FABL.DNFFormula.eval_eq_neg_one_iff`.
