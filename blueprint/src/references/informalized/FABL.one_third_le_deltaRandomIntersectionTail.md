<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/DNFFourier.lean :: FABL.one_third_le_deltaRandomIntersectionTail -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Random Intersection Tail Bound

**Claim.** For $0<\delta\leq1$, a positive integer $k$, and a finite set $U$ with $3k/\delta<|U|$, the weighted probability that a random subset intersects $U$ in at least $k$ elements is at least $1/3$.

**Proof.** Write $X=|U\cap J|$ for a random subset $J$ with the stated weights, let $\mu=\delta|U|$ be its mean, and set $a=\mu-k+1$. The size assumption gives $\mu>3k$, so $a>0$. Let $q$ be the total weight of subsets for which $X<k$. On this event, $a\leq\mu-X$, hence $a^2\leq(X-\mu)^2$. Since all weights are nonnegative, summing this pointwise bound over the failure event and then including the remaining nonnegative terms shows that $a^2q\leq\mathbb E[(X-\mu)^2]$. The weighted variance identity gives $\mathbb E[(X-\mu)^2]=\delta(1-\delta)|U|\leq\mu$. From $\mu>3k$ one obtains $3\mu\leq2a^2$; therefore $q\leq2/3$. The weights sum to one, and success and failure partition all subsets, so the weight of the event $X\geq k$ is $1-q\geq1/3$.

**Key facts.** `FABL.deltaRandomSubsetWeight_nonneg`, `FABL.sum_deltaRandomSubsetWeight_mul_sq_card_inter_sub_mean`, `FABL.sum_deltaRandomSubsetWeight`.
