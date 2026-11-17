<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/CodeFormat.lean :: Turing.CodeFormat.serialize_decode_length_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Serialization Length After Decoding

**Claim.** For any code format $F$ and bit string $\alpha$, the length of the serialization of the value obtained by decoding $\alpha$ is at most the larger of $|\alpha|$ and the serialization length of $F$'s fallback value.

**Proof.** Canonicalization equals serialization after decoding (`Turing.CodeFormat.canonical_eq`), so it suffices to bound the length of the canonical output. If scanning fails, canonicalization returns the fallback serialization, whose length is at most the stated maximum. If scanning succeeds with remainder $u$, canonicalization takes an initial segment of $\alpha$ of length $|\alpha|-|u|$. The length of a list prefix is at most the length of the original list, so this output has length at most $|\alpha|$, and hence at most the same maximum.

**Key facts.** `Turing.CodeFormat.canonical_eq`.
