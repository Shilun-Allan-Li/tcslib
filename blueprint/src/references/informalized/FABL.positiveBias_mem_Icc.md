<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/KKLBribery.lean :: FABL.positiveBias_mem_Icc -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bounds on Positive Bias

**Claim.** For every Boolean function on a finite sign cube, its positive bias lies in $[0,1]$.

**Proof.** The mean of a sign-valued function lies in $[-1,1]$ (`mean_toReal_mem_Icc`). By the identity expressing positive bias as $(1+\mathbb{E}[f])/2$ (`positiveBias_eq_mean`), adding $1$ and dividing by $2$ sends this interval to $[0,1]$.

**Key facts.** `FABL.positiveBias_eq_mean`, `FABL.mean_toReal_mem_Icc`.
