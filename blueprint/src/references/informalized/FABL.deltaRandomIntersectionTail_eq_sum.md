<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/DNFFourier.lean :: FABL.deltaRandomIntersectionTail_eq_sum -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Subset-sum formula for intersection tails

**Claim.** The weighted sum over subsets whose intersection with $U$ has size at least $k$ equals the stated sum over subsets contained in $U$, weighted by their size and by the size of their complement within $U$.

**Proof.** For each subset $J$, the tail indicator is one exactly when $|U\cap J|\ge k$. Rewrite that indicator by summing over all subsets $S$, retaining only the term $S=U\cap J$ and only when $|S|\ge k$. Summing first over $J$ and then over $S$ gives the same total as summing in the opposite order, since the sums are finite. For fixed $S$, the sum of the weights of those $J$ with $U\cap J=S$ is zero unless $S\subseteq U$; when $S\subseteq U$, it equals $\delta^{|S|}(1-\delta)^{|U\setminus S|}$ (`sum_deltaRandomSubsetWeight_inter_eq`). Keeping only the sets with $|S|\ge k$ yields the claimed formula.

**Key facts.** `FABL.sum_deltaRandomSubsetWeight_inter_eq`.
