<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clLeft_until -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Lifting a Run Before Exit

**Claim.** Up to and including time $t$, the host machine's run from the embedded starting configuration agrees with the embedded run of the original machine, provided the original run avoids the exit state at every time strictly before $t$.

**Proof.** Induct on the time $j\le t$. At time zero, the host configuration was defined to be the embedded starting configuration. For the successor step, assume the configurations agree at time $j$ and that $j+1\le t$. Let $z$ be the original machine's configuration at time $j$. The avoidance hypothesis ensures that $z$ is not in the exit state. If $z$ is halted, both machines stay at their respective configurations, so the embedded configurations still agree. If $z$ has state $q$, then $q$ differs from the exit state. By the transition hypothesis, the host transition at the embedded state is the original transition on the first $k$ tapes, extended to leave the additional tapes unchanged and to map the successor state by the embedding. The embedded configuration presents the same symbols on those first $k$ tapes as $z$ does. The compatibility of applying an extended action with embedding a configuration (`Turing.FinTM.leftCfg_apply`) now identifies the resulting configurations. The successor-time recurrence for runs (`Turing.MultiTapeTM.runFrom_succ_eq_step'`) supplies the transition step on both sides, completing the induction.

**Key facts.** `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Turing.FinTM.leftCfg_apply`.
