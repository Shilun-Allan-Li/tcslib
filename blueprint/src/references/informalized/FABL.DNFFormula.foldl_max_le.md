<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/DNFFormulas.lean :: FABL.DNFFormula.foldl_max_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bound on a Running Maximum

**Claim.** If every element of a finite list has its function value at most $B$, and the initial value is at most $B$, then folding the operation that takes the maximum with each function value produces a value at most $B.

**Proof.** Proceed by induction on the list. For the empty list, the fold returns the initial value, which is at most $B$. For a list with head $a$ and remaining list, the induction hypothesis applies to the remaining list with initial value $\max(a_0,f(a))$, where $a_0$ is the original initial value. Both entries of this maximum are at most $B$, so the new initial value is at most $B$; the induction hypothesis then bounds the completed fold by $B$.
