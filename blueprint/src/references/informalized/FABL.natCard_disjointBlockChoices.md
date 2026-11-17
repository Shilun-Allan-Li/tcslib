<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/MatchingMomentCombinatorics.lean :: FABL.natCard_disjointBlockChoices -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Count of disjoint block choices

**Claim.** For a finite set $R$ and natural numbers $d,t$, the number of ordered choices of $t$ pairwise disjoint subsets of $R$, each of size $d$, is $\displaystyle\prod_{j=0}^{t-1}\binom{|R|-jd}{d}$.

**Proof.** Proceed by induction on $t$, allowing the remaining finite set to vary. With no blocks to choose, there is one empty choice, and the product is empty, hence also one. For the induction step, choose the first block $B$ among the $d$-element subsets of $R$, then choose the remaining $t$ blocks from $R\setminus B$. Since $B\subseteq R$ and $|B|=d$, the remaining set has size $|R|-d$. By the induction hypothesis, the number of continuations for each such $B$ is $\prod_{j=0}^{t-1}\binom{|R|-(j+1)d}{d}$, independent of the particular block. There are $\binom{|R|}{d}$ choices for $B$. Multiplying this count by the continuation count gives the claimed product, with the first factor corresponding to $j=0$ and the rest to $j=1,\ldots,t$.
