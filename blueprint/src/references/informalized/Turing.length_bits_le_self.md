<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Encoding.lean :: Turing.length_bits_le_self -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bound on Binary Expansion Length

**Claim.** For every natural number $m$, the length of its binary expansion is at most $m$.

**Proof.** The length of the binary expansion is the binary size of $m$ (`Nat.size_eq_bits_len`). The bound that this size is at most $m$ follows from the characterization of size together with the elementary inequality $m<2^m$ (`Nat.size_le` and `Nat.lt_two_pow_self`).
