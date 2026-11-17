<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/CodeFormat.lean :: Turing.codeDecode_serialize_pad -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Decoder round-trip with padding

**Claim.** For every one-work-tape coded Turing machine and every natural number $m$, decoding its serialization followed by $m$ additional one-bits returns the original machine.

**Proof.** Apply the general padding round-trip theorem for a code format (`CodeFormat.decode_serialize_pad`) to the one-tape format and the machine in question. It states that decoding a machine’s serialization with any number of trailing one-bits recovers that machine. By definition, `codeDecode` is the one-tape format’s decoder, so this gives the claim.

**Key facts.** `Turing.CodeFormat.decode_serialize_pad`.
