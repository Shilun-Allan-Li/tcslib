<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Lib/Seg.lean :: Light.getD_readSeg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Entries of a read segment

**Claim.** For $i<n$, the entry at index $i$ in the list of memory values read from $a$ through $a+n-1$ is $\mu(a+i)$.

**Proof.** Because $i<n$, the requested entry is in the read segment. Reading it as a list entry rather than a defaulted entry therefore makes no difference. The defining entry formula for a read segment (`Light.getElem_readSeg`) identifies that entry with $\mu(a+i)$.

**Key facts.** `Light.getElem_readSeg`.
