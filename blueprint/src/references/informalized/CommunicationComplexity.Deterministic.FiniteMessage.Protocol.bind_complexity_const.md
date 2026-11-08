<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/DeterministicCC/DetComposition.lean :: CommunicationComplexity.Deterministic.FiniteMessage.Protocol.bind_complexity_const -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Complexity of constant-cost bind

**Claim.** If every continuation protocol has complexity $c$, then binding a finite-message protocol to those continuations adds $c$ to its complexity.

**Proof.** Proceed by induction on the protocol. If it immediately outputs $a$, binding selects the continuation $q(a)$; its complexity is $c$ by hypothesis, while the original protocol has complexity zero. Thus the result holds in this case. If Alice sends a message, the induction hypothesis says that each resulting continuation has complexity equal to its original complexity plus $c$. The protocol's complexity takes the supremum of these branch complexities and adds the cost of Alice's message. The supremum of a finite, nonempty family after adding the same constant is the original supremum plus that constant (finset_sup_add_const). Hence the total is the original protocol complexity plus $c$. The Bob-message case is identical: apply the induction hypothesis to each branch and use the same supremum identity.

**Key facts.** `CommunicationComplexity.Deterministic.FiniteMessage.Protocol.finset_sup_add_const`.
