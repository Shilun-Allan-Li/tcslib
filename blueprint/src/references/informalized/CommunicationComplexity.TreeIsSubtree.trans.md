<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/DeterministicCC/Trees.lean :: CommunicationComplexity.TreeIsSubtree.trans -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Transitivity of the Subtree Relation

**Claim.** If s is a subtree of t and t is a subtree of u, then s is a subtree of u.

**Proof.** Induct on the derivation that t is a subtree of u. If it is the reflexive case, then t=u, and the given relation from s to t is already the result. If u is a node and t is a subtree of its left child, the induction hypothesis composes the given relation from s to t with that child relation; the left-subtree constructor then shows s is a subtree of u. The right-child case is identical, using the right-subtree constructor.
