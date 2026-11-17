<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/ISCountMath.lean :: Complexity.LogProg.ISCount.gs_and -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Conjunction at the Terminal Condition

**Claim.** The recursive condition with terminal predicate $c'\mapsto \mathrm{Kont}(c')\land Q$ holds at $(r,t,c)$ exactly when the condition with terminal predicate $\mathrm{Kont}$ holds there and $Q$ holds.

**Proof.** Induct on the number $r$ of choices, allowing the starting position and counter to vary. When $r=0$, the recursive condition is just its terminal predicate, so the equivalence is the statement that $\mathrm{Kont}(c)\land Q$ is equivalent to $\mathrm{Kont}(c)\land Q$. For the successor case, unfold the first choice: either $A(t)$ holds and the remaining condition starts at $(t+1,c+1)$, or $B(t)$ holds and it starts at $(t+1,c)$. Apply the induction hypothesis to each remaining condition. In either branch, the resulting requirement is the corresponding recursive condition with terminal predicate $\mathrm{Kont}$ together with $Q$. Since $Q$ is common to both branches, the disjunction of these two cases is equivalent to the original recursive condition with terminal predicate $\mathrm{Kont}$ and $Q$ together.
