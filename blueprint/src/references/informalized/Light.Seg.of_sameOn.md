<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Lib/Seg.lean :: Light.Seg.of_sameOn -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Agreement on a Finite Segment

**Claim.** If $\mu'$ agrees with $\mu$ wherever $K$ holds, and $K(b+i)$ holds for every $i<|l|$, then $\mu'(b+i)=l_i$ for every such index.

**Proof.** A segment remains a segment when the two functions agree at each point sampled by its entries (Light.Seg.congr). At each $b+i$ with $i<|l|$, the hypothesis supplies $K(b+i)$, so the assumed agreement gives $\mu'(b+i)=\mu(b+i)$. The original segment property says $\mu(b+i)=l_i$. Thus the entries of $l$ are the corresponding values of $\mu'$.

**Key facts.** `Light.Seg.congr`.
