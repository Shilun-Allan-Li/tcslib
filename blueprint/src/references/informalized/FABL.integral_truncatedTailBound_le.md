<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/RademacherFirstMoment.lean :: FABL.integral_truncatedTailBound_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Integral bound for a truncated tail

**Claim.** If $1\le T$, and $g(t)=U$ for $t\le T$ while $g(t)=4e^{-t^2/2}$ for $t>T$, then $\int_{t>0}g(t)\,dt\le UT+4e^{-T^2/2}$.

**Proof.** Split the positive half-line into $(0,T]$ and $(T,\infty)$. The function is integrable there because the truncated-tail integrability result gives integrability on $(0,\infty)$ (`integrableOn_truncatedTailBound`). On $(0,T]$ it is constantly $U$, so its integral is $UT$. On $(T,\infty)$ it equals $4e^{-t^2/2}$. Since $T\ge1$ and $t>T$, the exponent inequality $-t^2/2\le -T^2/2+(T-t)$ holds: after rearrangement it follows from $(t-T)(t+T-2)\ge0$. Thus the Gaussian tail integrand is bounded above by $4e^{-T^2/2}e^{T-t}$. The latter has integral $4e^{-T^2/2}$ over $(T,\infty)$, by the elementary exponential integral. Adding the two pieces gives the asserted bound.

**Key facts.** `FABL.integrableOn_truncatedTailBound`.
