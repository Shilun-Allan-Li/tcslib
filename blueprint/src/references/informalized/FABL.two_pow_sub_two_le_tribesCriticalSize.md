<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/CoalitionalInfluenceAsymptotics.lean :: FABL.two_pow_sub_two_le_tribesCriticalSize -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Lower bound on critical tribe size

**Claim.** For every integer $w\ge4$, the critical tribe size is at least $2^{w-2}$.

**Proof.** The error in the expression for the critical size lies in $[\log 2/4,2]$ (`tribesCriticalSizeError_mem_Icc`), so in particular it is at most $2$. Also $\log 2\ge1/2$. Multiplying this last inequality by $2^w>0$ gives $(1/2)2^w\le (\log 2)2^w$. Since $w\ge4$, the natural-power identity $2^w=4\cdot2^{w-2}$ holds, and $2^{w-2}\ge2$. Using the formula $\mathrm{tribesCriticalSize}(w)=(\log 2)2^w-\mathrm{error}(w)$ (`tribesCriticalSize_eq_main_sub_error`), these estimates yield $\mathrm{tribesCriticalSize}(w)\ge 2^{w-2}$.

**Key facts.** `FABL.tribesCriticalSizeError_mem_Icc`, `FABL.tribesCriticalSize_eq_main_sub_error`.
