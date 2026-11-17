<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/DeterministicCC/Subprotocol.lean :: CommunicationComplexity.Deterministic.Protocol.erase_numLeaves -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Leaf Count After Erasing a Subprotocol

**Claim.** Erasing the subprotocol $s$ from $p$ produces a protocol with $L(p)-L(s)+1$ leaves, using truncated natural-number subtraction.

**Proof.** Choose a subprotocol path witnessing that $s$ lies in $p$. Erasure along this path has $p.numLeaves-s.numLeaves+1$ leaves by `erasePath_numLeaves`. Since `erase` is defined as erasure along the chosen path, unfolding that definition identifies its leaf count with the same quantity.

**Key facts.** `CommunicationComplexity.Deterministic.Protocol.erasePath_numLeaves`.
