<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Lib/Seg.lean :: Light.SegN.read -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Reading a segment value

**Claim.** If $\mu$ agrees with the natural-number list $l$, viewed as integers, on the segment from $a$, then for each $i<|l|$, $\mu(a+i)$ equals the integer represented by the $i$th entry of $l$.

**Proof.** The segment hypothesis identifies $\mu(a+i)$ with the entry at index $i$ of the integer-valued list obtained from $l$. Since $i<|l|$, the default value in the definition of $getD$ is not used: $l.getD\ i\ 0$ is exactly the entry at index $i$. Mapping to integers therefore gives the claimed equality.
