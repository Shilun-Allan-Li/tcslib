<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/Bank.lean :: Complexity.LogProg.le_bankK -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Work-Tape Bound for the Machine Bank

**Claim.** For each index in the finite set of machines, that machine's number of work tapes is at most the maximum number of work tapes in the collection.

**Proof.** The maximum is the supremum of the number of work tapes over all indices in the finite set. Since the chosen index belongs to that set, its value is at most this supremum, by the defining upper-bound property of a supremum over a finite set.
