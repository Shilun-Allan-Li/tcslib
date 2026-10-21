<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/DecisionTree.lean :: DecisionTree.length_deepPath -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: claude-opus-4-8; confidence: high -->

# The deepest path has length equal to the depth

**Claim.** For a decision tree $T$ on $n$ Boolean variables, the deepest root-to-leaf path $\mathrm{deepPath}(T)$ — the list of variables queried as one descends into the deeper of the two subtrees at every branch — has length exactly $\mathrm{depth}(T)$. In other words, the number of branch queries recorded along that path equals the recursively defined depth of the tree.

**Proof.** The argument is a direct structural induction on $T$, following the same recursion that defines both $\mathrm{depth}$ and $\mathrm{deepPath}$. Recall the two definitions in play. The depth is $\mathrm{depth}(\mathrm{leaf}\,b)=0$ and $\mathrm{depth}(\mathrm{branch}\,v\,\ell\,h)=1+\max(\mathrm{depth}(\ell),\mathrm{depth}(h))$. The deepest path is empty at a leaf, and at a branch it queries the branch variable $v$ and then continues into whichever subtree is at least as deep: $\mathrm{deepPath}(\mathrm{branch}\,v\,\ell\,h)=v\mathbin{::}\mathrm{deepPath}(h)$ when $\mathrm{depth}(\ell)\le\mathrm{depth}(h)$, and $v\mathbin{::}\mathrm{deepPath}(\ell)$ otherwise.

1. **Base case (leaf).** For $T=\mathrm{leaf}\,b$, the deepest path is the empty list, so its length is $0$, and $\mathrm{depth}(\mathrm{leaf}\,b)=0$ as well. The two sides are definitionally equal, so there is nothing to compute.

2. **Inductive step (branch).** Let $T=\mathrm{branch}\,v\,\ell\,h$, and assume the result for both subtrees: $\mathrm{deepPath}(\ell).\mathrm{length}=\mathrm{depth}(\ell)$ and $\mathrm{deepPath}(h).\mathrm{length}=\mathrm{depth}(h)$. Unfolding $\mathrm{deepPath}$ exposes the comparison $\mathrm{depth}(\ell)\le\mathrm{depth}(h)$, and we split on it.

3. **Case $\mathrm{depth}(\ell)\le\mathrm{depth}(h)$.** Here the path is $v\mathbin{::}\mathrm{deepPath}(h)$, so its length is $1+\mathrm{deepPath}(h).\mathrm{length}$ (the length of a cons is one more than the tail's length), which by the inductive hypothesis for $h$ equals $1+\mathrm{depth}(h)$. On the other side, $\mathrm{depth}(T)=1+\max(\mathrm{depth}(\ell),\mathrm{depth}(h))$, and since $\mathrm{depth}(\ell)\le\mathrm{depth}(h)$ the maximum is $\mathrm{depth}(h)$. Both sides are $1+\mathrm{depth}(h)$, so they agree.

4. **Case $\mathrm{depth}(\ell)>\mathrm{depth}(h)$.** Symmetrically, the path is $v\mathbin{::}\mathrm{deepPath}(\ell)$, of length $1+\mathrm{depth}(\ell)$ by the inductive hypothesis for $\ell$. Now the maximum in $\mathrm{depth}(T)=1+\max(\mathrm{depth}(\ell),\mathrm{depth}(h))$ is $\mathrm{depth}(\ell)$, so again both sides equal $1+\mathrm{depth}(\ell)$.

In each case the single branch variable prepended at the top of the tree accounts for the "$1+$" in the depth, and the inductive hypothesis handles the chosen subtree; the arithmetic resolving the $\max$ against the case hypothesis is immediate. This completes the induction.

**Caveat.** The definition of deepPath is not printed in the formal statement block; its leaf value (the empty list) and its branch recursion (prepend the branch variable, descend into the subtree selected by the test depth(lo) ≤ depth(hi)) are reconstructed from the proof, which determines them unambiguously — the base case closes by rfl, and the two split branches invoke the hi- and lo-side hypotheses respectively.
