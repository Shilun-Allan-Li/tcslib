<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Nondeterminism.lean :: Complexity.e3_find_congr -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# First-match search under predicate agreement

**Claim.** If two Boolean predicates agree on every element of a finite list $xs$, then searching for the first element satisfying either predicate returns the same optional element.

**Proof.** Induct on the list. For the empty list, both searches return no element. For a list with head $a$ and tail $xs$, the predicates agree at $a$, so either both searches select $a$ immediately or neither does. In the latter case, they search the tail; the predicates still agree on every element of that tail, and the induction hypothesis says those remaining searches agree. Hence the searches on the whole list return the same option.
