<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/HastadThreeSat.lean :: FABL.expectDeltaRandomSubset_intersection_eq_sum -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Subset intersection expectation formula

**Claim.** The weighted average of $g(S\cap K)$ over all subsets $K$ equals the sum over $J\subseteq S$ of $\rho^{|J|}(1-\rho)^{|S\setminus J|}g(J)$.

**Proof.** Expand the expectation as a sum over $K$. For each fixed $K$, insert a sum over all $J$ whose term is the weight of $K$ times $g(J)$ when $S\cap K=J$, and zero otherwise. Interchange the two finite sums, then factor out $g(J)$ from the inner sum over $K$. The inner sum is the total weight of subsets $K$ satisfying $S\cap K=J$. The intersection-weight identity (by `sum_deltaRandomSubsetWeight_inter_eq`), with the fixed set there taken to be $J$ and the intersected set to be $S$, says this is zero unless $J\subseteq S$; when that inclusion holds, it is $\rho^{|J|}(1-\rho)^{|S\setminus J|}$. Substitution gives the asserted sum.

**Key facts.** `FABL.sum_deltaRandomSubsetWeight_inter_eq`.
