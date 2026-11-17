<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/MeyerMachine.lean :: Complexity.Meyer.decodeSel_encodeSel -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Selector Encoding and Decoding

**Claim.** For a finite state type $S$ with decidable equality and any number $k$ of work tapes, encoding a selector as its Boolean indicator vector and then decoding that vector returns the original selector.

**Proof.** For a selector $\sigma$, its encoding is therefore a valid encoded selector: there exists a selector whose encoding is that vector, namely $\sigma$ itself. Thus decoding uses the chosen selector witnessing this existence. The encoding is injective (`encodeSel_injective`), so any selector with the same encoding as $\sigma$ must equal $\sigma$.

**Key facts.** `Complexity.Meyer.encodeSel_injective`.
