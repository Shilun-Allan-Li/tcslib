<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/DeterministicCC/FiniteMessage.lean :: CommunicationComplexity.Deterministic.FiniteMessage.Protocol.completeTreeAlice_complexity -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Complexity of the complete Alice-query tree

**Claim.** The complete tree that asks Alice the $d$ binary queries and then runs the protocol indexed by their answers has complexity $d$ plus the maximum complexity of its continuation protocols over all bit patterns.

**Proof.** Induct on $d$. When $d=0$, there is exactly one bit pattern, the empty pattern, and the complete tree is the corresponding continuation. Thus its complexity is the supremum over that singleton, as required. For the step from $d$ to $d+1$, the root asks one bit, so its complexity is one plus the maximum of the complexities of the two subtrees, corresponding to first answer false and first answer true. Apply the induction hypothesis to each subtree. Each has complexity $d$ plus the supremum over its length-$d$ continuations; adding the common $d$ to both entries of a maximum gives $d$ plus the maximum of those two suprema. Every length-$(d+1)$ bit pattern has exactly one of the two possible first bits, followed by an arbitrary length-$d$ pattern. Consequently, the supremum over all such patterns is precisely that maximum of the two suprema. Including the root query yields $(d+1)$ plus the full supremum, as claimed.
