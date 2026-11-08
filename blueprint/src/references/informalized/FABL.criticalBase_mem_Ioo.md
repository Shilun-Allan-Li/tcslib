<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Tribes.lean :: FABL.criticalBase_mem_Ioo -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Critical Base Bounds

**Claim.** For every positive natural number $w$, the real number $1-2^{-w}$ lies strictly between $0$ and $1$.

**Proof.** The critical inverse $2^{-w}$ lies in $(0,1/2]$ by the half-interval bound (`FABL.criticalInverse_mem_Ioc`). Thus it is positive and at most $1/2$. Subtracting it from $1$ gives a number at least $1/2$, hence strictly positive; positivity of the inverse also makes the result strictly less than $1$.

**Key facts.** `FABL.criticalInverse_mem_Ioc`.
