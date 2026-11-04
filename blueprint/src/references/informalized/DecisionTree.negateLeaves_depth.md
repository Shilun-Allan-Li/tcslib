<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching.lean :: DecisionTree.negateLeaves_depth -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: claude-opus-4-8; confidence: high -->

# Negating leaves preserves decision-tree depth

**Claim.** Let $T$ be a decision tree on $n$ Boolean variables, and let $T'$ be the tree obtained from $T$ by replacing the Boolean value at every leaf with its negation while leaving the entire branching structure — the variable queried at each internal node and the arrangement of subtrees — untouched. Then $\mathrm{depth}(T') = \mathrm{depth}(T)$.

**Proof.** The depth of a decision tree is defined by recursion on its structure: a leaf has depth $0$, and a branch node has depth $1 + \max(\mathrm{depth}(\text{lo}), \mathrm{depth}(\text{hi}))$, where $\text{lo}$ and $\text{hi}$ are its two subtrees. The leaf-negation operation is defined by the same recursion, descending through every branch node unchanged and flipping the Boolean stored at each leaf. The claim is immediate once one observes that negating leaves never creates, destroys, or rearranges a branch node, so it cannot touch the quantity that depth measures. We make this precise by structural induction on $T$, following exactly the two cases of the tree's definition.

1. **Leaf case.** Suppose $T$ is a leaf carrying some value $b$. Negating leaves turns it into the leaf carrying $\lnot b$, which is still a leaf. Both leaves have depth $0$ by definition, so $\mathrm{depth}(T') = 0 = \mathrm{depth}(T)$.

2. **Branch case.** Suppose $T$ is a branch node querying variable $v$ with subtrees $\text{lo}$ and $\text{hi}$. The induction hypotheses are that negating leaves preserves the depth of each subtree: $\mathrm{depth}(\text{lo}') = \mathrm{depth}(\text{lo})$ and $\mathrm{depth}(\text{hi}') = \mathrm{depth}(\text{hi})$, where $\text{lo}'$ and $\text{hi}'$ are the subtrees with their leaves negated. By definition of the operation, negating the leaves of $T$ yields the branch node that queries the same variable $v$ and has subtrees $\text{lo}'$ and $\text{hi}'$. Computing its depth from the definition and then substituting the two induction hypotheses,
\[
\mathrm{depth}(T') = 1 + \max\big(\mathrm{depth}(\text{lo}'),\, \mathrm{depth}(\text{hi}')\big) = 1 + \max\big(\mathrm{depth}(\text{lo}),\, \mathrm{depth}(\text{hi})\big) = \mathrm{depth}(T).
\]

This closes the induction, and the result holds for every decision tree $T$.
