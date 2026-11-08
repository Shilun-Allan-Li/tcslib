<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Lib/Seg.lean :: Light.SegN.getElem -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Values on a natural-number segment

**Claim.** If the values of $\mu$ starting at $a$ agree with the entries of $l$ viewed as integers, then for every $i<|l|$, $\mu(a+i)$ equals the integer represented by $l_i$.

**Proof.** Apply the assumed segment agreement at index $i$. Its list on the integer side is the image of $l$ under the natural-to-integer map. The entry at index $i$ of that mapped list is the image of the entry $l_i$, which gives the stated equality.
