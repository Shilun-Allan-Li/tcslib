<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/ISCountMath.lean :: Complexity.LogProg.ISCount.size_half -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Binary size under halving

**Claim.** For every nonzero natural number $m$, its binary size is one greater than the binary size of the quotient $m/2$.

**Proof.** Binary size is the length of the binary digit list. For nonzero $m$, the digits of the quotient $m/2$ are obtained by removing the first digit from the digit list of $m$ (`Nat.div2_bits_eq_tail`, together with the identification of division by two with `Nat.div2`). Since $m$ is nonzero, its binary digit list has positive length. Removing its first digit therefore decreases that length by exactly one, so the size of $m/2$ is the size of $m$ minus one. Rearranging gives the stated identity.
