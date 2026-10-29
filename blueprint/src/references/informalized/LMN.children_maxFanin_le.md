<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/RecursiveReduction.lean :: LMN.children_maxFanin_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: claude-opus-4-8; confidence: high -->

# Children Inherit the Fanin Bound

**Claim.** Let $g = \mathrm{node}(b, cs)$ be an internal gate of a Boolean circuit on $n$ variables — an AND gate if $b$ is true, an OR gate otherwise — applied to a list $cs$ of child circuits, and let $w$ be a natural number. The maximum fanin of $g$ is, by definition, the larger of the gate's own fanin $|cs|$ (the number of children) and the greatest maximum fanin occurring among the children. If $\mathrm{maxFanin}(g) \le w$, then every child circuit $c$ appearing in $cs$ satisfies $\mathrm{maxFanin}(c) \le w$.

**Proof.** We unfold the definition of the maximum fanin of a node and then isolate the one inequality that does the work.

1. **Unfolding the node.** By the defining equation of $\mathrm{maxFanin}$ on a node,
\[
\mathrm{maxFanin}\big(\mathrm{node}(b, cs)\big) \;=\; \max\!\big(|cs|,\ F(cs)\big),
\]
where $F(cs)$ is the aggregate of the children's maximum fanins, computed as the right fold
\[
F(cs) \;=\; \mathrm{foldr}\big(\lambda\, c\ a.\ \max(\mathrm{maxFanin}(c),\, a),\ 0,\ cs\big).
\]
Concretely, $F$ of the empty list is $0$, and $F(c_0 :: l) = \max\!\big(\mathrm{maxFanin}(c_0),\, F(l)\big)$; so $F(cs)$ is just the maximum of the children's maximum fanins (and $0$ if there are none). The hypothesis $\mathrm{maxFanin}(g) \le w$ thus reads $\max(|cs|, F(cs)) \le w$.

2. **Every child is dominated by the fold.** We claim that for any list $l$ of circuits and any $c$ with $c \in l$, we have $\mathrm{maxFanin}(c) \le F(l)$. This is proved by induction on $l$. If $l$ is empty, the membership $c \in l$ is impossible, so there is nothing to prove. If $l = c_0 :: l'$, then $F(l) = \max\!\big(\mathrm{maxFanin}(c_0),\, F(l')\big)$, and membership $c \in l$ splits into two cases. Either $c = c_0$, in which case $\mathrm{maxFanin}(c) = \mathrm{maxFanin}(c_0) \le \max(\mathrm{maxFanin}(c_0), F(l'))$ by the left part of the maximum; or $c \in l'$, in which case the induction hypothesis gives $\mathrm{maxFanin}(c) \le F(l')$, and this is in turn at most $\max(\mathrm{maxFanin}(c_0), F(l'))$ by the right part. Either way $\mathrm{maxFanin}(c) \le F(l)$. (This routine case analysis is what the Lean proof dispatches with its `induction … <;> aesop`.)

3. **Chaining the inequalities.** Apply the claim of step 2 to the actual child list, with $l = cs$ and our given child $c \in cs$, obtaining $\mathrm{maxFanin}(c) \le F(cs)$. Since $F(cs) \le \max(|cs|, F(cs))$ (the right-hand argument of a maximum never exceeds the maximum), and the latter is $\le w$ by the hypothesis of step 1, transitivity yields
\[
\mathrm{maxFanin}(c) \;\le\; F(cs) \;\le\; \max(|cs|, F(cs)) \;\le\; w,
\]
which is exactly the required bound $\mathrm{maxFanin}(c) \le w$. $\qed$
