<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Codec/Layout.lean :: Complexity.Codec.two_pow_bits_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Binary expansion length bound

**Claim.** For every natural number $L\ge1$, if $b$ is the length of its binary expansion, then $2^b\le 2L$.

**Proof.** Use the standard relation between binary length and size: $b=\mathrm{size}(L)$. Since $L\ge1$, its size is positive. By the defining threshold property of size, $L$ is not less than $2^{\mathrm{size}(L)-1}$. Also, $2^{\mathrm{size}(L)}=2\cdot 2^{\mathrm{size}(L)-1}$. Combining these gives $2^b\le 2L$.
