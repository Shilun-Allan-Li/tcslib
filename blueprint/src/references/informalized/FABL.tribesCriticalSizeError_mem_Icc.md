<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Tribes.lean :: FABL.tribesCriticalSizeError_mem_Icc -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Critical Size Error Bounds

**Claim.** For every positive integer $w$, the critical size error lies in $[\log 2/4,\,2]$.

**Proof.** Put $x=2^{-w}$, $L=-\log(1-x)$, and $A=(\log 2)/x=(\log 2)2^w$. The inverse parameter bound gives $0<x\le 1/2$ (`criticalInverse_mem_Ioc`). The logarithmic estimates give $x+x^2/2\le L$ (`criticalLog_lower`), $0<L$ (`criticalLog_pos`), and $L\le x/(1-x)$ (`criticalLog_upper`). These estimates place the threshold $T=(\log 2)/L$ between $A-\log 2$ and $A-\log 2/4$: for the upper bound on $T$, use $L\ge x+x^2/2$ and $0\le A-\log 2/4$ to obtain $(A-\log 2/4)L\ge \log 2$; for the lower bound, use $L\le x/(1-x)$ and $0\le A-\log 2$ to obtain $(A-\log 2)L\le\log 2$. By the candidate-threshold equivalence, the critical size is at most $T$ (`candidate_iff_cast_le_threshold`), and its floor characterization gives $T<\mathrm{tribesCriticalSize}(w)+1$ (`tribesCriticalSize_eq_floor_threshold`). Since the error is $A-\mathrm{tribesCriticalSize}(w)$, the threshold bounds imply it is at least $\log 2/4$ and at most $\log 2+1$. Finally $\log 2\le1$, so the upper bound is $2$.

**Key facts.** `FABL.criticalInverse_mem_Ioc`, `FABL.criticalLog_pos`, `FABL.criticalLog_lower`, `FABL.criticalLog_upper`, `FABL.candidate_iff_cast_le_threshold`, `FABL.tribesCriticalSize_eq_floor_threshold`.
