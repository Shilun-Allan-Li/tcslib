<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_catalogFind_congr -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Congruence of List Search

**Claim.** If two Boolean predicates agree on every element of a finite list, then searching that list for the first element satisfying either predicate gives the same result.

**Proof.** Induct on the list. For the empty list, neither predicate finds an element, so the results agree. For a list with head $a$ and tail $xs$, the predicates agree at $a$, since $a$ belongs to the list. If they both accept $a$, both searches return it. If they both reject $a$, each search continues on $xs$; the hypotheses still imply agreement at every element of that tail, so the induction hypothesis gives equal results there. Hence the searches agree on the whole list.
