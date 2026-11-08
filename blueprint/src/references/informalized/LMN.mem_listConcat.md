<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/CircuitCompression.lean :: LMN.mem_listConcat -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Membership in a concatenated list

**Claim.** An element belongs to the concatenation of a list of lists exactly when it belongs to one of the lists in that collection.

**Proof.** Induct on the list of lists. For the empty collection, the concatenation is empty and there is no constituent list, so both sides are false. For a nonempty collection with first list $l$ and remaining collection $ls$, concatenation is $l$ followed by the concatenation of $ls$. Membership therefore means either membership in $l$ or membership in the tail concatenation. By the induction hypothesis, the latter means membership in some list of $ls$. Together these alternatives are precisely membership in some list of the full collection.
