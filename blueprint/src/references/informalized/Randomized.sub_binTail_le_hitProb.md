<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/RandomWalkMixingPad.lean :: Randomized.sub_binTail_le_hitProb -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Hitting probability comparison

**Claim.** For every $m,j$ and starting vertex $s$, the original graph's probability of hitting $t$ after $j$ steps, minus the binomial tail $B_D(m,j)$, is at most the padded graph's probability of hitting $t$ after $m$ steps, assuming $n\le D$.

**Proof.** We induct on $m$. The condition $n\le D$ and the nonemptiness of the vertex set ensure $D\ge1$, so the padded walk's recurrence is valid. For $m=0$, when $j=0$ both sides reduce to the same indicator of whether $s=t$. When $j>0$, the binomial tail is $1$; the original hitting probability is at most $1$, and the padded probability is nonnegative, giving the inequality.

Now suppose the claim holds at $m$ and consider $m+1$. If $s=t$, the padded walk has already hit its target, so its probability is $1$; the desired bound follows because the original probability is at most $1$ and the binomial tail is nonnegative. For $s\ne t$ and $j=0$, the original probability is zero, so nonnegativity of the padded probability suffices. For $j>0$, first consider a vertex with no out-neighbors. Its original hitting probability remains zero by the zero-outdegree fact (`hitProb_mk_eq_zero`); the claim then follows from nonnegativity of the padded probability and the binomial tail.

It remains to treat $s\ne t$ with positive outdegree $d$. The original one-step recurrence expresses its $j+1$ step hitting probability as the average of the $j$ step probabilities over its $d$ out-neighbors (`hitProb_mk_succ`). Write these probabilities as $R$, and write $b_1=B_D(m,j)$ and $b_2=B_D(m,j+1)$. The induction hypothesis bounds each out-neighbor's probability minus $b_1$ by that neighbor's padded $m$ step hitting probability. At $s$, the same hypothesis bounds $R-b_2$ by its padded probability. Summing the first inequalities over the $d$ neighbors and multiplying the second by $D-d\ge0$ gives a lower bound on the sum over all $D$ padded slots: the slots represent the genuine out-neighbors together with $D-d$ self-loops. This accounting is precisely the padded-slot sum identity (`sum_padNbr`). The average identity for the original walk and the bound on $d$ used here follow from the definitions and the fact that there are at most $n\le D$ vertices.

Finally, the recurrence for $B_D$ combines $b_1$ and $b_2$ with weights $1/D$ and $1-1/D$. The tail is nondecreasing in its second argument (`binTail_mono`), so $b_1\le b_2$; also $1\le d\le D$. Hence $(d-1)(b_1-b_2)\le0$. Rearranging this inequality and the preceding padded-slot bound gives exactly the claimed recurrence step.

**Key facts.** `Randomized.RegularMultigraph.hitProb_nonneg`, `Randomized.RegularMultigraph.hitProb_succ`, `Randomized.RegularMultigraph.hitProb_zero`, `Randomized.binTail_mem_Icc`, `Randomized.binTail_mono`, `Randomized.hitProb_mk_eq_zero`, `Randomized.hitProb_mk_mem_Icc`, `Randomized.hitProb_mk_succ`, `Randomized.sum_padNbr`.
