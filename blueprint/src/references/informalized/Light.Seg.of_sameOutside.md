<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Lib/Seg.lean :: Light.Seg.of_sameOutside -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Agreement Outside a Segment

**Claim.** If $\mu'$ agrees with $\mu$ outside $[a,a+n)$ and the segment starting at $b$ lies wholly before that interval or at or after its endpoint, then $\mu'(b+i)=l_i$ for every $i<|l|$.

**Proof.** A segment remains valid when its two functions agree at each point sampled by its entries (Light.Seg.congr). For each $i<|l|$, the separation hypothesis ensures that $b+i$ is outside $[a,a+n)$: if $b+|l|\le a$, then $b+i<a$; if $a+n\le b$, then $a+n\le b+i$. Hence the assumed outside agreement gives $\mu'(b+i)=\mu(b+i)$, and the original segment property identifies this value with $l_i$.

**Key facts.** `Light.Seg.congr`.
