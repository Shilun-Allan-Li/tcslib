<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/RandomWalkHitting.lean :: Randomized.RegularMultigraph.le_of_energy -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Energy Bound on Vertex Values

**Claim.** Under the stated nonnegativity, boundary, local-average, and reachability assumptions, every value of $F$ is at most $2D|V|^3$.

**Proof.** Let $n=|V|$, choose a vertex $s$ where $F$ is maximal, and write $M=F(s)$. If $M\le0$, nonnegativity and maximality give the result immediately. Suppose $M>0$. Define the total edge energy $S=\sum_x\sum_i(F(x)-F(G.\mathrm{nbr}(x,i)))^2$. The energy identity expresses this as $2D\sum_x F(x)(F(x)-\operatorname{avg}F(x))$ (`sum_sq_eq_energy`). At the distinguished vertex $t$ the summand is zero; at every other vertex the local hypothesis bounds it above by $F(x)$. Since $F(x)\le M$, it follows that $S\le 2D nM$.

Choose an edge slot $(x_0,i_0)$ with maximal absolute difference $a=|F(x_0)-F(G.\mathrm{nbr}(x_0,i_0))|$. Each squared edge difference is at most the total energy, so $a^2\le S$. Reachability from $s$ to $t$ gives a walk of length less than $n$ (`exists_short_walk`). Along each edge the change in $F$ is at most $a$, so the telescoping bound along this walk gives $|F(s)-F(t)|\le \operatorname{length}(p)a$ (`abs_sub_le_length_mul`). As $F(t)=0$ and $M>0$, this yields $M\le na$. Combining the estimates gives $M^2\le n^2S\le 2Dn^3M$; dividing by the positive $M$ yields $M\le2Dn^3$. Maximality then gives the same bound for every $F(u)$.

**Key facts.** `Randomized.RegularMultigraph.sum_sq_eq_energy`, `Randomized.RegularMultigraph.exists_short_walk`, `Randomized.RegularMultigraph.abs_sub_le_length_mul`.
