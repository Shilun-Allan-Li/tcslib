<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/RandomRestrictions.lean :: FABL.sum_deltaRandomSubsetWeight_inter_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Intersection-constrained weight sum

**Claim.** For subsets $S,U$ of the $n$ coordinates, the total weight of subsets $J$ satisfying $U\cap J=S$ is $\delta^{|S|}(1-\delta)^{|U\setminus S|}$ when $S\subseteq U$, and is zero otherwise.

**Proof.** First suppose $S\subseteq U$. Set $B=U\setminus S$ and $R=[n]\setminus U$. These three sets $S,B,R$ are pairwise disjoint and cover all coordinates. The condition $U\cap J=S$ says precisely that $J=S\cup L$ for a unique subset $L\subseteq R$: the coordinates in $S$ must be chosen, those in $B$ must be excluded, and the coordinates in $R$ are free. Thus the constrained sum becomes a sum over $L\subseteq R$. Since $S$ and $L$ are disjoint, $|S\cup L|=|S|+|L|$, and the covering partition gives $n-|S\cup L|=|B|+|R\setminus L|$. Each summand consequently factors as $\delta^{|S|}(1-\delta)^{|B|}$ times $\delta^{|L|}(1-\delta)^{|R\setminus L|}$. Factoring out the first term leaves the total random subset weight on $R$, which is $1$ by the product expansion of $\prod_{i\in R}(\delta+(1-\delta))$. The result is the claimed expression, since $B=U\setminus S$. If $S\nsubseteq U$, no intersection $U\cap J$ can equal $S$, because any such intersection is contained in $U$ (subset-of-intersection fact, `FABL.subset_of_inter_eq_left`). Every summand is then zero.

**Key facts.** `FABL.subset_of_inter_eq`, `FABL.subset_of_inter_eq_left`.
