<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/RandomRestrictions.lean :: FABL.sum_deltaRandomSubsetWeight_mem -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Weight of subsets containing a coordinate

**Claim.** For any coordinate $i$ among the $n$ coordinates, the weights of all subsets containing $i$ sum to $\delta$.

**Proof.** Let $R=[n]\setminus\{i\}$. Every subset containing $i$ has a unique form $\{i\}\cup K$ with $K\subseteq R$. Its weight is $\delta^{|K|+1}(1-\delta)^{|R|-|K|}$, because $i\notin K$ and $|R|=n-1$. Factor out $\delta$ and sum over $K\subseteq R$. The remaining sum is $1$: expanding $\prod_{j\in R}(\delta+(1-\delta))$ enumerates exactly those terms and every factor equals $1$. Hence the original sum is $\delta$.
