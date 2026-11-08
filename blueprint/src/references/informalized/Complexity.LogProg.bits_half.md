<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/FragDec.lean :: Complexity.LogProg.bits_half -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Halving a Binary Expansion

**Claim.** For every natural number $n$, the binary bit list of $\lfloor n/2\rfloor$ is the tail of the binary bit list of $n$.

**Proof.** The natural-number division-by-two operation `div2` agrees with division by $2$. Rewriting $n/2$ as `Nat.div2 n` therefore reduces the claim to the standard identity that the bits of `div2 n` are the tail of the bits of $n$ (`Nat.div2_bits_eq_tail`).
