<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/NPReductions/ThreeSATToClique.lean :: ThreeSATToClique.no_conflict_of_true -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# True literals do not conflict

**Claim.** If two literals both evaluate to true under an assignment, then they do not conflict.

**Proof.** A conflict can occur only when one literal is positive and the other is negative, with the same variable. If the positive literal is true, the assignment makes that variable true, so the negative literal is false, a contradiction. The reverse ordering gives the same contradiction. Thus two true literals cannot conflict.
