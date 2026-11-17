<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Util/List.lean :: List.take_succ_getD -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# A list prefix through a specified entry

**Claim.** If $i$ is less than the length of $l$, then the first $i+1$ entries of $l$ consist of its first $i$ entries followed by the entry at position $i$.

**Proof.** The prefix of length $i+1$ is the prefix of length $i$ with the next entry appended. Since $i$ lies within the list, the default value is not used: the default-valued lookup agrees with the actual entry at position $i$. Hence the appended singleton is exactly the entry specified in the claim.
