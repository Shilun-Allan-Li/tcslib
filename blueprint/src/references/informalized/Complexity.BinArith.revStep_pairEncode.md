<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/BinaryArith/Mul.lean :: Complexity.BinArith.revStep_pairEncode -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Reversal Step on Encoded Pairs

**Claim.** For any bit strings $u$ and $v$, one reversal step yields an encoded pair whose reversed first component followed by its second component equals $u$ reversed followed by $v$, while preserving total length and shortening the first component when it is nonempty.

**Proof.** If $u$ is empty, take $u'$ empty and $v'=v$. The step leaves the encoded pair unchanged, and all the stated identities follow. If $u=b::u_0$, take $u'=u_0$ and $v'=b::v$. The step removes the first bit of the first component and prepends it to the second, so the new encoding is exactly the result of the step. Reversing $u_0$ and then appending $b::v$ gives the reversal of $b::u_0$ followed by $v$. The removed bit is transferred without loss, so the sum of the component lengths is unchanged, while the first component's length drops by one.
