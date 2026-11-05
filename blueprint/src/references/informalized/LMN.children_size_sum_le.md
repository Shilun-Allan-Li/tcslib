<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/RecursiveReduction.lean :: LMN.children_size_sum_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: claude-opus-4-8; confidence: high -->

# The Children of a Gate Are Strictly Smaller

**Claim.** Let $g = \mathrm{node}(\mathit{isAnd}, cs)$ be an internal gate of a Boolean circuit on $n$ variables, where $cs$ is the list of its child subcircuits, and let $s$ be a natural number with $\mathrm{size}(g) \le s$. Then the total size of the children, $\sum_{c \in cs} \mathrm{size}(c)$, is at most $s - 1$, where the subtraction is truncated natural-number subtraction.

**Proof.** The whole argument rests on the definition of size for an internal gate: a node counts itself once and then adds the sizes of its children, so
\[
\mathrm{size}(g) \;=\; \mathrm{size}\bigl(\mathrm{node}(\mathit{isAnd}, cs)\bigr) \;=\; 1 + \sum_{c \in cs} \mathrm{size}(c).
\]
(Here $\sum_{c \in cs} \mathrm{size}(c)$ denotes the right fold `cs.foldr (fun c acc => c.size + acc) 0`.) Because the gate contributes its own unit $1$ on top of the children, the total size of the children is *strictly* smaller than the size of $g$:
\[
\sum_{c \in cs} \mathrm{size}(c) \;<\; 1 + \sum_{c \in cs} \mathrm{size}(c) \;=\; \mathrm{size}(g).
\]
This strict inequality is just $m < 1 + m$ for a natural number $m$; the Lean proof discharges it by splitting on whether $cs$ is empty or not, purely so that the definition of size unfolds in each shape, after which the arithmetic is immediate — no mathematical content hides in that case split. Chaining this strict bound with the hypothesis $\mathrm{size}(g) \le s$ by transitivity gives
\[
\sum_{c \in cs} \mathrm{size}(c) \;<\; s.
\]
Finally, for natural numbers $a < b$ implies $a \le b - 1$ even under truncated subtraction: if $a < b$ then $b \ge 1$, so passing to $b - 1$ loses nothing. Applying this with $a = \sum_{c \in cs} \mathrm{size}(c)$ and $b = s$ yields the claim, $\sum_{c \in cs} \mathrm{size}(c) \le s - 1$.
