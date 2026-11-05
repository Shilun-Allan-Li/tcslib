<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/DecisionTreeFourier.lean :: DecisionTree.size_le_two_pow_depth -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: claude-opus-4-8; confidence: high -->

# Size of a Decision Tree is at Most Two to the Depth

**Claim.** Let $T$ be a decision tree on $n$ Boolean variables, where $\mathrm{size}(T)$ counts the leaves of $T$ and $\mathrm{depth}(T)$ is its depth (a leaf has depth $0$, and a branch has depth one more than the larger of its two subtrees' depths). Then $\mathrm{size}(T) \le 2^{\mathrm{depth}(T)}$. In words: a decision tree of depth $k$ can have at most $2^{k}$ leaves.

**Proof.** The argument is a structural induction on the tree $T$, following the two ways a decision tree can be built: as a single leaf, or as a branch on a variable with two subtrees.

1. **Leaf.** A leaf $T$ holds a single Boolean value. By definition $\mathrm{size}(T) = 1$ and $\mathrm{depth}(T) = 0$, so the claim reads $1 \le 2^{0} = 1$, which holds.

2. **Branch.** Suppose $T$ branches on a variable $x_i$ into a "low" subtree $L$ and a "high" subtree $H$, and assume as induction hypotheses that
   \[
   \mathrm{size}(L) \le 2^{\mathrm{depth}(L)}, \qquad \mathrm{size}(H) \le 2^{\mathrm{depth}(H)}.
   \]
   Write $m = \max(\mathrm{depth}(L), \mathrm{depth}(H))$, so that $\mathrm{depth}(T) = 1 + m$ and $\mathrm{size}(T) = \mathrm{size}(L) + \mathrm{size}(H)$.

3. **Pass to the common exponent $m$.** Since $2^{(\cdot)}$ is monotone in its exponent and $\mathrm{depth}(L), \mathrm{depth}(H) \le m$, we have $2^{\mathrm{depth}(L)} \le 2^{m}$ and $2^{\mathrm{depth}(H)} \le 2^{m}$. Chaining these with the induction hypotheses gives $\mathrm{size}(L) \le 2^{m}$ and $\mathrm{size}(H) \le 2^{m}$.

4. **Add and collapse.** Adding the two bounds,
   \[
   \mathrm{size}(T) = \mathrm{size}(L) + \mathrm{size}(H) \;\le\; 2^{m} + 2^{m} \;=\; 2^{\,1+m} \;=\; 2^{\mathrm{depth}(T)},
   \]
   where the middle equality is just $2 \cdot 2^{m} = 2^{m+1}$. This is the desired bound for $T$, completing the induction.
