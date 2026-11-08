<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Lib/Seg.lean :: Light.Seg.keep -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Preserving a Segment Under Agreement

**Claim.** If $\mu'$ agrees with $\mu$ throughout the interval $[a,a+|l|)$, then $l$ is also a segment of the values of $\mu'$ starting at $a$.

**Proof.** The congruence property of segments says that a segment remains valid when the two functions agree at every point sampled by its entries (Light.Seg.congr). For each $i<|l|$, the point $a+i$ lies in $[a,a+|l|)$, so the assumed agreement gives $\mu'(a+i)=\mu(a+i)$. The original segment property identifies the latter with $l_i$, establishing the segment property for $\mu'$.

**Key facts.** `Light.Seg.congr`.
