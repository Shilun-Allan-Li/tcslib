<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/CircuitHelpers.lean :: LMN.depth_le_two_children_depth_le_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: claude-opus-4-8; confidence: high -->

# Children of a depth-two gate have depth at most one

**Claim.** Let $g = \mathrm{node}(\mathit{isAnd}, cs)$ be a Boolean tree circuit consisting of a single gate — an AND gate if $\mathit{isAnd}$ holds, an OR gate otherwise — applied to a list $cs$ of child circuits, and suppose $\mathrm{depth}(g) \le 2$. Then every child circuit $c$ occurring in $cs$ satisfies $\mathrm{depth}(c) \le 1$.

**Proof.** Recall the depth convention: a literal has depth $0$, and a gate node has depth
\[
\mathrm{depth}(\mathrm{node}(\mathit{isAnd}, cs)) \;=\; 1 + \big(\textstyle\mathrm{foldr}\ \max\ 0\big)(cs),
\]
where $(\mathrm{foldr}\ \max\ 0)(cs)$ is the running maximum of the child depths, taken to be $0$ on the empty list. Concretely, on a nonempty list $c :: cs$ this unfolds to $\max\big(\mathrm{depth}(c),\ (\mathrm{foldr}\ \max\ 0)(cs)\big)$. So the stated hypothesis $\mathrm{depth}(g) \le 2$ is exactly the statement that the maximum child depth is at most $1$; the content of the lemma is to distribute that single bound over the individual children.

The proof is by induction on the list $cs$. One point is worth flagging about the Lean route: the depth hypothesis $\mathrm{depth}(g) \le 2$ mentions $cs$, so the induction is really carried out on the *implication* "if $\mathrm{depth}(\mathrm{node}(\mathit{isAnd}, cs)) \le 2$ then every child in $cs$ has depth $\le 1$", with the bound re-supplied in each case. This matters because the inductive hypothesis must be applied to a shorter list with its *own* (weaker) depth bound, which we derive along the way.

1. **Base case, $cs = [\,]$.** There are no children, so "every $c \in cs$ has depth $\le 1$" holds vacuously, independently of the hypothesis. (The depth of the empty gate is $1 + 0 = 1$, well under the bound, but this is not even needed.)

2. **Inductive step, $cs = c :: cs'$.** The inductive hypothesis is: *if* $\mathrm{depth}(\mathrm{node}(\mathit{isAnd}, cs')) \le 2$, then every child in $cs'$ has depth $\le 1$. The current hypothesis, after unfolding the depth of the cons, reads
\[
1 + \max\big(\mathrm{depth}(c),\ (\mathrm{foldr}\ \max\ 0)(cs')\big) \;\le\; 2,
\]
equivalently $\max\big(\mathrm{depth}(c),\ (\mathrm{foldr}\ \max\ 0)(cs')\big) \le 1$. From a bound on a maximum we read off a bound on each argument: $\mathrm{depth}(c) \le 1$ and $(\mathrm{foldr}\ \max\ 0)(cs') \le 1$.

3. We must show $\mathrm{depth}(x) \le 1$ for every $x \in c :: cs'$. Membership splits into two cases. If $x = c$, this is the first inequality from Step 2. If $x \in cs'$, we invoke the inductive hypothesis; its premise $\mathrm{depth}(\mathrm{node}(\mathit{isAnd}, cs')) \le 2$ amounts to $1 + (\mathrm{foldr}\ \max\ 0)(cs') \le 2$, which follows from the second inequality $(\mathrm{foldr}\ \max\ 0)(cs') \le 1$ of Step 2. The inductive hypothesis then delivers $\mathrm{depth}(x) \le 1$.

Both cases give the required bound, completing the induction. The only arithmetic used throughout is that $1 + m \le 2 \iff m \le 1$ and that $\max(a,b) \le 1$ entails $a \le 1$ and $b \le 1$ — the small natural-number reasoning the Lean proof discharges automatically.
