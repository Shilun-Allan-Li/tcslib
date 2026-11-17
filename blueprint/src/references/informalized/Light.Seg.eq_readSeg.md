<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Lib/Seg.lean :: Light.Seg.eq_readSeg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Recovering a segment by reading values

**Claim.** A list that records the values of $\mu$ starting at $a$ is exactly the list of those values read over its length.

**Proof.** The two lists have the same length: the list of values is formed from a range whose length is the original list's length. To establish equality, compare entries at any position $i$ within that length. The entry in the list of values is $\mu(a+i)$ (Light.getElem_readSeg), and the segment condition says the original entry is also $\mu(a+i)$. Hence the lists agree entry by entry and are equal.

**Key facts.** `Light.getElem_readSeg`.
