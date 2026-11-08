<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Lib/Seg.lean :: Light.Seg.drop -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Dropping an initial segment

**Claim.** Dropping the first $k$ entries of a list that records the values of $\mu$ starting at $a$ gives a list recording the values starting at $a+k$.

**Proof.** Let $i$ be a position within the dropped list. Then $k+i$ is within the original list. Its entry there equals $\mu(a+(k+i))$ by the original segment condition. The entry at position $i$ after dropping $k$ entries is precisely the original entry at position $k+i$, and $a+(k+i)=(a+k)+i$. Thus the dropped list records the values starting at $a+k$.
