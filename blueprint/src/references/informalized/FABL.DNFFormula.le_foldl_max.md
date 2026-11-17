<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/DNFFormulas.lean :: FABL.DNFFormula.le_foldl_max -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# List Values Are Bounded by the Running Maximum

**Claim.** For every element of a finite list, its function value is at most the result of folding the maximum operation over that list from any initial value.

**Proof.** Induct on the list, considering an element $a$ that belongs to it. There is no such element for the empty list. For a list with head $b$, if $a=b$, then $f(a)$ is at most the first updated accumulator, $\max(acc,f(b))$, and that accumulator is at most the final fold value (`le_foldl_max_aux`). If $a$ occurs in the tail, apply the induction hypothesis to the tail, starting with the updated accumulator $\max(acc,f(b))$.

**Key facts.** `FABL.DNFFormula.le_foldl_max_aux`.
