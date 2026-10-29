<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/CircuitHelpers.lean :: LMN.depth_le_one_children_are_lits -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: claude-opus-4-8; confidence: high -->

# Depth-one gates have only literal children

**Claim.** Let $C = g(c_1,\dots,c_k)$ be a tree circuit on $n$ variables consisting of a single gate $g$ (AND or OR, recorded by a Boolean flag $\mathrm{isAnd}$) applied to a list of child circuits $c_1,\dots,c_k$. If $\mathrm{depth}(C)\le 1$, then every child $c_i$ in the list is a literal: there is a literal $\ell_i$ (a variable index in $\{0,\dots,n-1\}$ together with a polarity) with $c_i = \ell_i$.

**Proof.** Recall the depth convention used here: a literal has depth $0$, and a gate node has depth
\[
  \mathrm{depth}\bigl(g(c_1,\dots,c_k)\bigr) \;=\; 1 + \max_{1\le i\le k}\mathrm{depth}(c_i),
\]
where the maximum is realised concretely as a right fold of $\max$ over the child list seeded at $0$ (so an empty list contributes $0$). Write $M$ for that fold, so $\mathrm{depth}(C) = 1 + M$. Fix an arbitrary child $c$ occurring in the list; we must produce a literal equal to $c$. The argument has three steps.

1. **The fold dominates each member.** First we record the evident fact that $M$ is an upper bound for the depth of every circuit in the list: if $c$ occurs in a list $l$, then the right fold of $\max$ over $l$ (seeded at $0$) is at least $\mathrm{depth}(c)$. This is a routine induction on $l$. The empty list cannot contain $c$, so the base case is vacuous; in the step case the fold over $x :: l'$ is $\max\bigl(\mathrm{depth}(x),\,\text{fold over } l'\bigr)$, and $c$ is either $x$ — making the first argument of the $\max$ exactly $\mathrm{depth}(c)$ — or a member of $l'$, in which case the inductive hypothesis bounds the second argument below by $\mathrm{depth}(c)$. Either way the $\max$ is at least $\mathrm{depth}(c)$.

2. **The child has depth zero.** Applying step 1 to our fixed child gives $M \ge \mathrm{depth}(c)$. Suppose, towards a contradiction, that $\mathrm{depth}(c) > 0$. Then $M \ge \mathrm{depth}(c) \ge 1$, so
\[
  \mathrm{depth}(C) \;=\; 1 + M \;\ge\; 2,
\]
contradicting the hypothesis $\mathrm{depth}(C) \le 1$. Hence $\mathrm{depth}(c)$ is not positive, and being a natural number it must equal $0$. (In the Lean text this is $\mathrm{depth}(c)\le 0$ from "not greater than $0$", combined with $0 \le \mathrm{depth}(c)$ to give equality.)

3. **Depth zero forces a literal.** Finally we inspect the two possible shapes of $c$. If $c$ is a literal $\ell$, we are done immediately. If instead $c$ were itself a gate node $g'(d_1,\dots,d_m)$, then by the depth formula $\mathrm{depth}(c) = 1 + (\text{fold over its children}) \ge 1 > 0$, contradicting step 2. So the node case is impossible, and $c$ must be a literal, as required.

The route is the natural one: rather than reasoning about the maximum abstractly, the proof first proves the pointwise domination of the fold by a short list induction, uses it to pin the child's depth to $0$, and then reads off from the definition of depth that only literals have depth $0$.
