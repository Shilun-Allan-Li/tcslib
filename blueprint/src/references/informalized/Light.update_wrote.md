<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Regions.lean :: Light.update_wrote -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Updating outside a written interval

**Claim.** If $y$ lies outside the interval from $dst$ through $dst+j-1$, then updating the function obtained by writing the first $j$ values of $f$ starting at $dst$ at $y$ agrees with first updating the original memory at $y$ and then writing that interval.

**Proof.** Compare both functions at an arbitrary index $a$. If $a=y$, the update on the left assigns $w$ directly. On the right, the write leaves the already updated memory unchanged at $y$, because $y$ is outside the written interval (`Light.wrote_rest`); its value is therefore also $w$. If $a\ne y$, both updates leave the value at $a$ unchanged. The two sides then apply the same write rule there, so their values agree whether $a$ belongs to the written interval or not.

**Key facts.** `Light.wrote_rest`.
