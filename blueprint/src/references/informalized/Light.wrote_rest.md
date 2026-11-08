<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Regions.lean :: Light.wrote_rest -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Values outside the written interval

**Claim.** If $a<dst$ or $dst+j\le a$, then the function that writes values of $f$ on $dst\le x<dst+j$ has value $\mu(a)$ at $a$.

**Proof.** The condition says either that $a$ is below the interval or that it is at or beyond its upper endpoint. In either case, $a$ does not satisfy both inequalities defining the written interval. The write rule therefore selects the unchanged value $\mu(a)$.
