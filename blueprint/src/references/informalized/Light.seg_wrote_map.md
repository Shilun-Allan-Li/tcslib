<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Lib/Pass.lean :: Light.seg_wrote_map -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# A mapped list in a written interval

**Claim.** The values of the sequence written from $d$ using the mapped entries of $L$ agree with the list obtained by applying $g$ to each entry of $L$.

**Proof.** Apply the preceding result about written intervals to the list $L.map\ g$. Its length is $|L|$. At any valid index $i$, the mapped list has entry $g(L_i)$. Because $i$ is valid for $L$, the defaulted lookup $L.getD\ i\ 0$ is the actual entry $L_i$. Thus the write function uses $g(L_i)$ at the corresponding offset, as required by the written-interval result. The resulting sequence agrees with $L.map\ g$.

**Key facts.** `Light.seg_wrote`.
