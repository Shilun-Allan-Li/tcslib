<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Rules.lean :: Light.Ends.pieceThen -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Sequential Composition with an Intermediate Condition

**Claim.** If $s_1$ executes within $T_1$ to a state satisfying $R$, and from every such state $s_2$ executes within $T-T_1$ to a state satisfying $Q$, then $s_1;s_2$ executes within $T$ to a state satisfying $Q$, provided $T_1\le T$.

**Proof.** First use `Light.Ends.mono` with no increase in the first cost bound to strengthen the first execution’s postcondition: each state satisfying $R$ is now required to satisfy that $s_2$ has an execution within $T-T_1$ ending in $Q$. Then apply the sequential-composition principle `Light.Ends.next`, which joins this first execution to the promised second execution and uses $T_1\le T$ to fit their bounds into the total budget $T$.

**Key facts.** `Light.Ends.mono`, `Light.Ends.next`.
