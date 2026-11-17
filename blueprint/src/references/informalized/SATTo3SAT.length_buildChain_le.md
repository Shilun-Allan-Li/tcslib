<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/NPReductions/SATTo3SAT.lean :: SATTo3SAT.length_buildChain_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Chain Length Bound

**Claim.** For every list of literals and starting counter, the chain encoding has length at most the length of the list.

**Proof.** We induct on the list. The empty list produces no clauses. When the list has one or two elements, the defining cases produce at most one clause, so the bound is immediate. For a list with at least three elements, the definition emits one clause and continues with the tail at the next counter. The induction hypothesis bounds the remaining chain by the tail’s length; adding the emitted clause gives at most the length of the original list.
