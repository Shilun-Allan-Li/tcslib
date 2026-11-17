<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/BinaryArith/Loops.lean :: Complexity.BinArith.eq_encodeNat_of_hasFalse -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Decomposition at the First Zero

**Claim.** If a bit string $w$ contains at least one zero, then it is a string of $|H|$ consecutive ones followed by zero and then $R$, where $H$ and $R$ are the outputs of the specified first and second transducers from their initial states.

**Proof.** Proceed by induction on the string. The empty string cannot contain a zero. For a string beginning with zero, the required decomposition follows directly: the first transducer emits nothing, while the second outputs the remaining string, so the initial block has length zero. For a string beginning with one, the tail still contains a zero, by the characterization of `hasFalse` (Complexity.BinArith.hasFalse_cons). Apply the induction hypothesis to that tail. On adding the leading one, the first transducer adds one output bit and the second leaves its output unchanged (Complexity.BinArith.uHead_true_cons and Complexity.BinArith.uRest_true_cons). Thus the run of ones grows by one, while the zero and the remaining suffix are preserved, giving the required decomposition.

**Key facts.** `Complexity.BinArith.hasFalse_cons`, `Complexity.BinArith.uHead_true_cons`, `Complexity.BinArith.uRest_true_cons`.
