<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Regions.lean :: Light.wrote_done -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Values written on an interval

**Claim.** For $i<j$, the function obtained by writing values of $f$ on the interval $dst\le a<dst+j$ has value $f(i)$ at $dst+i$.

**Proof.** At $a=dst+i$, the index is at least $dst$, and $i<j$ implies $dst+i<dst+j$. Thus this index lies in the written interval, so the function takes the value $f((dst+i)-dst)$. Cancellation gives $(dst+i)-dst=i$, yielding $f(i)$.
