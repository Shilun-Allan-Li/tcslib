<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Tribes.lean :: FABL.tribesCriticalProbabilityDeficit_mem_Icc -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Critical probability deficit bounds

**Claim.** For every positive integer $w$, the critical probability deficit lies between $0$ and $2^{-w}$, inclusive.

**Proof.** Put $s$ equal to the critical size, $x=2^{-w}$, and $q=1-x$. The base bounds give $0<x\le\tfrac12$ (`criticalInverse_mem_Ioc`) and $0<q<1$ (`criticalBase_mem_Ioo`). The critical size satisfies the candidate inequality (`tribesCriticalSize_spec`), so $q^s\ge\tfrac12$. By the candidate-threshold equivalence and the floor characterization of the critical size (`candidate_iff_cast_le_threshold`, `tribesCriticalSize_eq_floor_threshold`), the next integer $s+1$ fails the candidate condition. Hence $q^{s+1}<\tfrac12$. The probability-deficit formula (`tribesCriticalProbabilityDeficit_eq_pow`) identifies the deficit with $q^s-\tfrac12$, which is nonnegative by the first bound. Since $q^s\le1$, multiplication by $x\ge0$ gives $q^s x\le x$; and $q^{s+1}=q^s(1-x)<\tfrac12$ gives $q^s-\tfrac12<q^s x$. Thus the deficit is at most $x=2^{-w}$, as required.

**Key facts.** `FABL.criticalInverse_mem_Ioc`, `FABL.criticalBase_mem_Ioo`, `FABL.tribesCriticalSize_spec`, `FABL.candidate_iff_cast_le_threshold`, `FABL.tribesCriticalSize_eq_floor_threshold`, `FABL.tribesCriticalProbabilityDeficit_eq_pow`.
