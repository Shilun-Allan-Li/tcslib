<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/RandomWalkMixing.lean :: Randomized.RegularMultigraph.walkDist_add -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Composition of Walk Distributions

**Claim.** Walking for $a+b$ steps from a rational vertex weight function gives the same distribution as walking first for $a$ steps and then for $b$ steps.

**Proof.** Induct on $a$, allowing the starting weight function to vary throughout the induction. If $a=0$, the zero-step identity says that the initial weights are unchanged (`Randomized.RegularMultigraph.walkDist_zero`), and $0+b=b$. For the successor case, rewrite $(a+1)+b$ as $(a+b)+1$. Apply the one-step recurrence to express this as first taking $a+b$ steps and then one step; the induction hypothesis replaces the first part by taking $a$ steps and then $b$ steps. Applying the same one-step recurrence in reverse combines those final stages into $b+1$, as required.

**Key facts.** `Randomized.RegularMultigraph.walkDist_zero`, `Randomized.RegularMultigraph.walkDist_succ`.
