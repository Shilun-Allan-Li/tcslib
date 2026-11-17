<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/RandomRestrictions.lean :: FABL.sum_deltaRandomSubsetWeight_supset -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Total weight of supersets

**Claim.** For a subset $S$ of the $n$ coordinates, the weights of all subsets $J$ containing $S$ sum to $\delta^{|S|}$.

**Proof.** Let $R=[n]\setminus S$. Every $J\supseteq S$ has a unique representation $J=S\cup K$ with $K\subseteq R$. Since $S$ and $K$ are disjoint, $|J|=|S|+|K|$, and $n-|J|=|R|-|K|$. Thus the weight of $J$ is $\delta^{|S|}$ times $\delta^{|K|}(1-\delta)^{|R|-|K|}$. Summing over $K\subseteq R$ factors out $\delta^{|S|}$. The remaining sum is $1$, as it is the expansion of $\prod_{j\in R}(\delta+(1-\delta))$, whose factors all equal $1$.
