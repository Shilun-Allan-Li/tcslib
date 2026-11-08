<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/RandomRestrictions.lean :: FABL.sum_deltaRandomSubsetWeight -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Total random subset weight

**Claim.** For every nonnegative integer $n$ and real number $\delta$, the weights $\delta^{|J|}(1-\delta)^{n-|J|}$ of all subsets $J$ of the $n$ coordinates sum to $1$.

**Proof.** Rewrite each weight as a product: each coordinate in $J$ contributes $\delta$, and each coordinate outside $J$ contributes $1-\delta$. The sum over all subsets is therefore the sum over the powerset of the products associated with each choice of the two contributions. Expanding the product $\prod_{i=1}^n(\delta+(1-\delta))$ gives exactly this sum. Every factor equals $1$, so the product, and hence the sum, is $1$.
