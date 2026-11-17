<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/Basic.lean :: BoolCircuit.TreeCircuit.depth_le_maxDepth -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Depth Bounded by Maximum List Depth

**Claim.** If a circuit $c$ occurs in a list $cs$, then its depth is at most the maximum depth of the circuits in $cs$, with the empty-list maximum taken to be zero.

**Proof.** Proceed by induction on the list, using the membership hypothesis. For a list with head $c$, the head case follows because the maximum of the head's depth and the remaining maximum is at least the head's depth. If $c$ occurs in the tail, the induction hypothesis bounds its depth by the tail maximum, and that maximum is at most the maximum of the head depth and the tail maximum. The empty list has no member, so there is no case to prove there.
