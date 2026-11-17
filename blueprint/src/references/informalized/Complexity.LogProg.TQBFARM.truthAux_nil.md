<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/TQBFARM/Semantics.lean :: Complexity.LogProg.TQBFARM.truthAux_nil -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Truth for an Empty Matrix

**Claim.** For every finite quantifier prefix, Boolean assignment, and index, the quantified truth predicate for the empty CNF matrix holds.

**Proof.** Induct on the quantifier prefix, allowing the assignment and index to vary. With no quantifiers, the empty CNF evaluates to true, so the claim holds directly. If the first quantifier is existential, choose the value false; the induction hypothesis applies to the updated assignment and next index. If it is universal, take an arbitrary Boolean value and apply the induction hypothesis to the corresponding updated assignment and next index. In either case the quantified truth condition follows.
