<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/GotsmanLinialExtremizer.lean :: FABL.tendsto_sqrt_shift_mul_oddMajorityInfluence -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: low -->

# Scaled Majority Influence Limit

**Claim.** For each positive natural number $d$, the product of $\sqrt{2m+d}$ and the odd-majority influence at $m$ tends to $\sqrt{2/\pi}$ as $m\to\infty$.

**Proof.** First, $(2m+d)/(2m+1)\to1$, by the limit for affine quotients. Continuity of the square-root function therefore gives $\sqrt{(2m+d)/(2m+1)}\to1$. The proof next uses an algebraic identity for the auxiliary main-term expression: multiplying $\sqrt{2m+d}$ by that expression gives $\sqrt{2/\pi}\,\sqrt{(2m+d)/(2m+1)}$. Consequently, the product with the main term tends to $\sqrt{2/\pi}$. Finally, the odd-majority influence divided by its main term tends to $1$ (`FABL.tendsto_oddMajorityInfluence_div_main`). Multiplying these convergent factors yields the claimed limit.

**Key facts.** `FABL.tendsto_oddMajorityInfluence_div_main`.

**Caveat.** The proof uses the auxiliary expression `oddMajorityInfluenceMain` and its defining formula, but neither is included in the supplied upstream statements. The algebraic identity is specified in the proof source, though its definition cannot be checked from the payload.
