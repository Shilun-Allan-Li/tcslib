<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/CodeFormat.lean :: Turing.CodeFormat.decode_serialize_pad -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Decoding a Padded Serialization

**Claim.** For every code $M$ and natural number $m$, decoding the serialization of $M$ followed by $m$ copies of the bit $1$ returns $M$.

**Proof.** The parser recognizes the serialization followed by any finite padding of $1$s: it returns the pair consisting of $M$ and that padding (`Turing.CodeFormat.parseFull_serialize_pad`). Decoding takes the code component of this successful parse, so it returns $M$.

**Key facts.** `Turing.CodeFormat.parseFull_serialize_pad`.
