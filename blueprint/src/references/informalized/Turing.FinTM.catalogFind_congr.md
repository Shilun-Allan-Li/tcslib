<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Primitives.lean :: Turing.FinTM.catalogFind_congr -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Extensionality of List Search

**Claim.** If two Boolean predicates agree on every element of a list, then searching that list for the first element satisfying either predicate gives the same optional result.

**Proof.** Proceed by induction on the list. The empty list has no element to return, so both searches agree. For a list with head $a$ and tail $xs$, the predicates agree at $a$, so either both searches return $a$ or both continue into the tail. In the latter case, they still agree on every element of the tail, and the induction hypothesis says the tail searches return the same result. Thus the searches on the original list agree.
