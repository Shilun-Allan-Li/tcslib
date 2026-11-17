<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/NARMCompile.lean :: Complexity.LogProg.ndtm_runWith_eq_runFrom -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Agreement of Runs on Choice Words

**Claim.** If the nondeterministic machine and deterministic machine agree on every state outside $X$, and the deterministic run avoids $X$ during its first $T$ steps, then every choice word of length at most $T$ produces the same configuration in the nondeterministic run as the deterministic run does after that many steps.

**Proof.** Induct on the choice word, allowing the starting configuration and time bound to vary. The empty word leaves the configuration unchanged, so the claim holds immediately. For a nonempty word $b::w$, its length bound implies $T$ is positive; write $T=T'+1$. If the current configuration is halted, both machines leave it unchanged. Otherwise its state is some $q$, and the avoidance hypothesis at time zero gives $\neg X(q)$. Thus, for the first choice bit $b$, the two transition actions agree, and so the configurations after one step agree. The deterministic run-from-succesor identity (`Turing.MultiTapeTM.runFrom_succ_eq_step`) expresses its remaining $T'$-step run as the original run after one step followed by $T'$ steps. At each later time $t<T'$, the original run is at time $t+1<T$, so it still avoids $X$. The induction hypothesis applies to the tail word $w$ and the new configuration, proving agreement after $|w|$ further steps. Together these give agreement after $|b::w|$ steps.

**Key facts.** `Turing.NDTM.runWith_cons`, `Turing.NDTM.stepWith_of_halt`, `Turing.MultiTapeTM.step_of_halt`, `Turing.MultiTapeTM.runFrom_succ_eq_step`.
