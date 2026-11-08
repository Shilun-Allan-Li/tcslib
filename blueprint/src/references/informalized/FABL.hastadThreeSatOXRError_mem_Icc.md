<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/HastadThreeSat.lean :: FABL.hastadThreeSatOXRError_mem_Icc -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Three-SAT OXR Error Range

**Claim.** For every natural number $t$ and every $[0m\varepsilon\in[0,1]$, the three-SAT OXR error at parameters $t$ and $\varepsilon$ lies in $[0,1]$.

**Proof.** Split according to whether $\varepsilon<1$. In that case, the hypothesis $\varepsilon\le 1$ gives $1-\varepsilon\ge0$, so the denominator power is nonnegative and the quantity under the square root is nonnegative. Its square root, divided by $4$, is therefore nonnegative. The minimum of this number and $1$ is nonnegative and at most $1$. If $\varepsilon<1$ fails, the definition gives the value $1$ directly, which also lies in the interval.
