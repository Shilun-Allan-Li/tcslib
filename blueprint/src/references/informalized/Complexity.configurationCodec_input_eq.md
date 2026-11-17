<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/TQBF.lean :: Complexity.configurationCodec_input_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Input Recovery from Configuration Encodings

**Claim.** If configurations on two Boolean inputs of length $n$ have equal configuration encodings, then the inputs are equal.

**Proof.** The length hypotheses select the genuine encoding branch for both configurations. The coefficient bound ensures that the code word represents every row-bit coordinate (`codecBit_card_le`), so equality of the code words implies equality of their bit functions (`codecWord_eq_iff`). Injectivity of the row-bit map then yields equality of the two rows (`codecRowBits_injective`). Their input fields are therefore equal, and equality of those fields implies equality of the original fixed-length inputs (`codecRowOf_input_eq`).

**Key facts.** `Complexity.codecBit_card_le`, `Complexity.codecWord_eq_iff`, `Complexity.codecRowBits_injective`, `Complexity.codecRowOf_input_eq`.
