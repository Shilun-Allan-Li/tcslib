<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/ComposedMajorityInfluence.lean :: FABL.totalInfluence_composedMajority_upper -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Upper bound for composed majority influence

**Claim.** For every natural number $m$, the total influence of the composed majority function is at most $2\sqrt{2m+3}$.

**Proof.** Set $T=2m+1$ and $D=2m+3$. The exact influence formula is $I_m=1+\frac12\sqrt{2/\pi}\sqrt T+E_m$, where $E_m\le 1/(2\sqrt T)$. Since $T\ge1$, we have $1\le\sqrt T$, so $E_m\le1/2$. The coefficient bound $\sqrt{2/\pi}\le1$ therefore gives $I_m\le\frac32+\frac12\sqrt T$. As $T\ge1$, this is at most $2\sqrt T$, and the square-root dimension comparison $\sqrt T\le\sqrt D$ gives $I_m\le2\sqrt D$, as required.

**Key facts.** `FABL.sqrt_majorityTail_le_composedMajority_dimension`, `FABL.composedMajorityInfluenceError_mem_Icc`, `FABL.sqrt_two_div_pi_le_one`, `FABL.totalInfluence_composedMajority_eq_main_add_error`.
