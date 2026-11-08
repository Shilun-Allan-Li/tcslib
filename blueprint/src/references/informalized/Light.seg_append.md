<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Lib/Seg.lean :: Light.seg_append -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Segments of concatenated lists

**Claim.** The memory segment beginning at $a$ agrees with $l_1++l_2$ if and only if it agrees with $l_1$ beginning at $a$ and with $l_2$ beginning at $a+|l_1|$.

**Proof.** Suppose the segment agrees with $l_1++l_2$. For an index in the range of $l_1$, the corresponding entry of the concatenation is the same entry of $l_1$, so the first segment agreement follows. For an index $i$ in the range of $l_2$, use index $|l_1|+i$ in the concatenation: its entry is the $i$th entry of $l_2$, and the memory address there is $a+|l_1|+i$. This gives the second agreement. Conversely, assume both segment agreements. At any valid index in the concatenation, split into two cases. If the index is less than $|l_1|$, the concatenation entry is from $l_1$ and the first agreement applies. Otherwise, subtract $|l_1|$ to obtain a valid index in $l_2$; the concatenation entry is then the corresponding entry of $l_2$, and the second agreement applies at the shifted address. In each case the memory value equals the required concatenation entry.
