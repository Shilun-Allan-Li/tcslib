<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Switching/CanonicalDTree.lean :: SwitchingLemma.termSubTree_deepPath_head_free -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: claude-opus-4-8; confidence: high -->

# Head of the Deepest Path Through a Free-Variable Term Sub-Tree

**Claim.** Fix a restriction $\rho$ on $n$ variables and a continuation $c$ assigning a decision tree to each restriction. Let $l$ be a literal whose variable $v$ is free in $\rho$ (that is, $\rho(v)$ is undefined), and let $\mathit{rest}$ be a further list of literals. Then there is a Boolean value $b$ such that the deepest root-to-leaf path of the term sub-tree built from $l :: \mathit{rest}$, $\rho$, and $c$ begins with the pair $(v, b)$ and continues with the deepest root-to-leaf path of the term sub-tree built from $\mathit{rest}$, the restriction $\rho$ amended so that $v$ is fixed to $b$, and the same continuation $c$.

**Proof.** The proof is a direct computation in two steps, one unfolding and one case split; the value of $b$ is read off from which branch is deeper.

1. **Unfold the sub-tree at a free variable.** Because $v$ is free in $\rho$, building the term sub-tree from the non-empty list $l :: \mathit{rest}$ branches on $v$ rather than skipping the literal: the result is the tree
\[
\mathrm{branch}\bigl(v,\; T_{\mathrm{false}},\; T_{\mathrm{true}}\bigr),
\qquad
T_b := \mathrm{termSubTree}\bigl(\mathit{rest},\; \rho[v \mapsto b],\; c\bigr),
\]
where $\rho[v \mapsto b]$ is $\rho$ with the value at $v$ overwritten by $b$. This is exactly the content of the unfolding lemma for a free leading literal (`termSubTree_cons_free`): the low child records the choice $v = \mathrm{false}$ and the high child records $v = \mathrm{true}$.

2. **Read off the head from the deepest path.** By definition, the deepest path of a branch descends into whichever child is at least as deep, breaking ties in favour of the high (true) child. Concretely, it equals $(v, \mathrm{true}) :: T_{\mathrm{true}}.\mathrm{deepPath}$ when $\mathrm{depth}(T_{\mathrm{true}}) \ge \mathrm{depth}(T_{\mathrm{false}})$, and $(v, \mathrm{false}) :: T_{\mathrm{false}}.\mathrm{deepPath}$ otherwise.

3. **Choose $b$ by the case.** In the first case take $b = \mathrm{true}$; in the second take $b = \mathrm{false}$. In either case the head of the deepest path is the pair $(v, b)$, and its tail is the deepest path of $T_b = \mathrm{termSubTree}(\mathit{rest}, \rho[v \mapsto b], c)$. This is precisely the asserted decomposition, so the chosen $b$ witnesses the existential. The crucial alignment is that the branch label $b$ carried into the path is the same Boolean to which $v$ is fixed in the restriction labelling that child — a consequence of how the branch was built in Step 1 — so no mismatch can occur.

**Key facts.** `SwitchingLemma.termSubTree_cons_free`.
