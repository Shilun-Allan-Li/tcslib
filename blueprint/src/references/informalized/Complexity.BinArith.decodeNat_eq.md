<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/BinaryArith/Loops.lean :: Complexity.BinArith.decodeNat_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Natural-Number Decoder Characterization

**Claim.** For every bit string $w$, decoding it as a natural number and residual word yields the pair consisting of the length of the head transducer's output and the rest transducer's output when $w$ contains a false bit; if it contains no false bit, decoding is undefined.

**Proof.** Induct on the bit string. The empty string satisfies the identity directly. For a string beginning with false, the natural-number decoder immediately returns zero and the remaining string; the head and rest transducers, and the predicate detecting a false bit, give the same result. For a string beginning with true, the decoder recursively processes the tail and increases the decoded number by one. The head transducer prepends one output bit, increasing its output length by one, while the rest transducer leaves its output unchanged. The predicate for containing a false bit reduces to that predicate on the tail, so the induction hypothesis gives the desired equality in both cases: if the tail contains a false bit, the returned pair agrees, and otherwise both sides are undefined.

**Key facts.** `Complexity.BinArith.hasFalse_cons`, `Complexity.BinArith.uHead_true_cons`, `Complexity.BinArith.uRest_true_cons`.
