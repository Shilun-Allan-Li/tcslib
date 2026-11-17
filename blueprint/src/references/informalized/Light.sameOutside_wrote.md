<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Regions.lean :: Light.sameOutside_wrote -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Writes preserve outside values

**Claim.** If $j\le n$, writing the values $f(0),\ldots,f(j-1)$ into the $j$ cells starting at $dst$ leaves memory unchanged at every address outside the interval from $dst$ through $dst+n-1$.

**Proof.** Take any address $b$ outside the interval from $dst$ through $dst+n-1$. Thus either $b<dst$ or $dst+n\le b$. Since $j\le n$, either alternative implies that $b$ is outside the shorter write interval from $dst$ through $dst+j-1$. The fact that a write leaves memory unchanged outside its own interval (`Light.wrote_rest`) therefore gives the desired equality of the written memory and the original memory at $b$.

**Key facts.** `Light.wrote_rest`.
