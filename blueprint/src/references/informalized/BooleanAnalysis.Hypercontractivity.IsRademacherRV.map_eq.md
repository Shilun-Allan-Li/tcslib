<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/RandomVariables/Basic.lean :: BooleanAnalysis.Hypercontractivity.IsRademacherRV.map_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Distribution of a Rademacher Variable

**Claim.** A Rademacher random variable has distribution equal to the equally weighted sum of point masses at $1$ and $-1$.

**Proof.** Let $s\subseteq\mathbb R$ be measurable. Since $r$ is almost surely either $1$ or $-1$, split into four cases according to whether each of these two values belongs to $s$. If both belong, the preimage $r^{-1}(s)$ agrees almost everywhere with the whole space, so its measure is $1$. If only $1$ belongs, that preimage agrees almost everywhere with $\{r=1\}$, of measure $1/2$. If only $-1$ belongs, it agrees almost everywhere with $\{r=-1\}$, also of measure $1/2$. If neither belongs, the preimage is null. In each case this equals the value on $s$ of the measure consisting of half a point mass at each of $1$ and $-1$. Equality on every measurable set proves equality of the measures.
