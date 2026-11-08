<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/RandomWalkMixingPad.lean :: Randomized.half_le_hitProb_padGraph -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Hit Probability After Bounded-Degree Padding

**Claim.** If $n\le D\le4n^2$ and a length-$k$ walk in the graph of a symmetric relation on $\mathrm{Fin}(n)$ hits $t$ from $s$ with probability at least $9/10$, then the length-$10n^2k$ walk in the padded regular multigraph of degree $D$ hits $t$ with probability at least $1/2$.

**Proof.** Since $s\in\mathrm{Fin}(n)$, we have $n>0$, so $D\ge n\ge1$. Write $m=10n^2k$ and let $b=\mathrm{binTail}(D,m,k)$. The comparison theorem for padded walks (`Randomized.sub_binTail_le_hitProb`) says that the padded hit probability is at least the original hit probability minus $b$. The tail estimates give $0\le b\le1$ (`Randomized.binTail_mem_Icc`) and $(m+1)b\le kD$ (`Randomized.succ_mul_binTail_le`). Using $D\le4n^2$, the latter implies $kD\le4n^2k$. Since $m=10n^2k$, these inequalities imply $b\le2/5$ (also when $k=0$). Therefore the padded hit probability is at least $9/10-2/5=1/2$.

**Key facts.** `Randomized.binTail_mem_Icc`, `Randomized.sub_binTail_le_hitProb`, `Randomized.succ_mul_binTail_le`.
