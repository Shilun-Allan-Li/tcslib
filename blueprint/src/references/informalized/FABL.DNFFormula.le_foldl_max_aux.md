<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/DNFFormulas.lean :: FABL.DNFFormula.le_foldl_max_aux -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# The Running Maximum Bounds Its Initial Value

**Claim.** Folding the maximum operation over any finite list, starting from $a$, produces a value at least $a$.

**Proof.** Induct on the list. For the empty list, the fold is exactly $a$. For a list with head $b$, the first updated value is $\max(a,f(b))$, which is at least $a$; applying the induction hypothesis to the tail shows that the final fold is at least this updated value, and hence at least $a$.
