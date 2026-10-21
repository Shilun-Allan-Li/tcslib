<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/GateMerge.lean :: LMN.reidx_eval_mergeGates_right -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: claude-opus-4-8; confidence: high -->

# Right embedding evaluates through the merged assignment

**Claim.** Let $m_1,m_2$ be natural numbers, let $c$ be a Boolean circuit on $m_2$ variables, and let $g_1:\mathbb{F}_2^{m_1}$ and $g_2:\mathbb{F}_2^{m_2}$ be Boolean assignments. Form the merged assignment on $m_1+m_2$ variables that reads off $g_1$ on indices $0,\dots,m_1-1$ and $g_2$ on indices $m_1,\dots,m_1+m_2-1$, and re-index $c$ along the right embedding $i\mapsto m_1+i$ of $\mathrm{Fin}\,m_2$ into $\mathrm{Fin}\,(m_1+m_2)$. Then evaluating the re-indexed circuit under the merged assignment returns exactly $c(g_2)$: the value of the original circuit under $g_2$ alone.

**Proof.** The whole statement collapses to a single observation about the merged assignment, once a general fact about re-indexing is brought to bear.

1. **Re-indexing is precomposition on the assignment.** The governing fact is that re-indexing a circuit and then evaluating it is the same as evaluating the original circuit under the precomposed assignment: for any map $f:\mathrm{Fin}\,m\to\mathrm{Fin}\,m'$ and any assignment $g:\mathrm{Fin}\,m'\to\{\mathrm{true},\mathrm{false}\}$,
\[
\bigl(\mathrm{reidx}(c,f)\bigr)(g) \;=\; c\,(g\circ f)
\]
(`BoolCircuit.TreeCircuit.reidx_eval`). Intuitively, re-indexing only renames the variable that each literal reads, so feeding $g$ to the renamed circuit is the same as feeding each literal the value $g$ assigns to its new name — that is, feeding the original circuit the composite $g\circ f$. Applying this with $f$ the right embedding $i\mapsto m_1+i$ and $g$ the merged assignment turns the left-hand side into
\[
c\bigl((\text{merged assignment})\circ(i\mapsto m_1+i)\bigr).
\]

2. **Reduce to equality of assignments.** Since both sides are now $c$ evaluated at some assignment, it suffices to show the two assignments agree — that is,
\[
(\text{merged assignment})\circ(i\mapsto m_1+i) \;=\; g_2 .
\]
Equality of functions on $\mathrm{Fin}\,m_2$ is checked pointwise, so fix $i\in\mathrm{Fin}\,m_2$.

3. **The right block of the merge is $g_2$.** The right embedding sends $i$ to the index of value $m_1+i$ in $\mathrm{Fin}\,(m_1+m_2)$. The merged assignment is defined by a case split on whether its argument is $<m_1$: if so it reads $g_1$, otherwise it reads $g_2$ at the shifted-down index. Here the argument has value $m_1+i \ge m_1$, so it is not below $m_1$ and the $g_2$ branch is taken, at index $(m_1+i)-m_1 = i$. Hence the composite assigns $g_2(i)$ at $i$, which is exactly $g_2$ evaluated at $i$. This holds for every $i$, giving the required equality of assignments, and with it the claim.

**Key facts.** `BoolCircuit.TreeCircuit.reidx_eval`.
