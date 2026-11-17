<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/BinaryArith/AddSub.lean :: Complexity.BinArith.serial_bounds -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bounds for Decoded Binary Values

**Claim.** Each decoded component of a string $z$, with failed decoding interpreted as empty, has value less than $2^{|z|+2}$.

**Proof.** For either decoded component, a bit string of length $k$ has binary value less than $2^k$ (Complexity.LogProg.bitsVal_lt_two_pow). The decoded first and second components each have length at most $|z|$ (Complexity.length_pairFstD_le and Complexity.length_pairSndD_le). Since powers of $2$ increase with the exponent, each value is therefore less than or equal to the corresponding bound $2^{|z|}$, which in turn is strictly less than $2^{|z|+2}$.

**Key facts.** `Complexity.LogProg.bitsVal_lt_two_pow`, `Complexity.length_pairFstD_le`, `Complexity.length_pairSndD_le`.
