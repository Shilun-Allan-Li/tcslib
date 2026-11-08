<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/RademacherFirstMoment.lean :: FABL.integrableOn_truncatedTailBound -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Integrability of a Truncated Tail Bound

**Claim.** For $T\ge 0$, the function equal to $U$ on $t\le T$ and to $4\exp(-t^2/2)$ on $t>T$ is integrable on $(0,\infty)$.

**Proof.** Split $(0,\infty)$ into $(0,T]$ and $(T,\infty)$. On the first interval the function is the constant $U$, which is integrable because the interval has finite length. On the second interval it agrees with $4\exp(-t^2/2)$, an integrable Gaussian function on the real line and hence integrable on that subinterval. The two intervals cover $(0,\infty)$ when $T\ge0$, and integrability on their union follows by combining these two integrable restrictions.
