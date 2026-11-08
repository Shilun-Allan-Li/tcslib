<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/LowDegreeJuntaLearning.lean :: FABL.anfCoeff_eq_zero_of_update_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Invariant coordinate gives zero coefficient

**Claim.** If $f$ is unchanged when coordinate $i$ is set to $1$ rather than $0$, and $i$ belongs to $S$, then the algebraic normal form coefficient of $f$ at $S$ is $0$.

**Proof.** Remove $i$ from $S$ and call the resulting set $R$, so $S=R\cup\{i\}$ and $i\notin R$. The subsets of $S$ split into two disjoint families: subsets $T$ of $R$, and sets $T\cup\{i\}$ for $T\subseteq R$. The map $T\mapsto T\cup\{i\}$ is injective on subsets of $R$, and every subset in the second family arises this way. In the coefficient sum, these paired terms cancel: the indicator cube of $T\cup\{i\}$ is obtained from that of $T$ by changing coordinate $i$ from $0$ to $1$, while all other coordinates agree. The assumed invariance makes the function values equal. Each value therefore appears twice, which sums to $0$ in $\mathbb F_2$.

**Key facts.** `FABL.f₂CubeOfFinset_apply`.
