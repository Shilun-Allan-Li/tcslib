<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/EXP.lean :: Complexity.enumCont_halt_transfer -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Transfer of halted runs

**Claim.** If the stop machine agrees with the original machine away from the designated state and loops there without changing the configuration, then a run of the stop machine that has halted by time $T$ yields the same configuration for the original machine at time $T$. The original run also avoids the designated state at every time $j\le T$.

**Proof.** First show that the stop machine cannot be in state $q_a$ at any time $j\le T$. Write $T=j+r$. If it were in $q_a$ at time $j$, the absorbing-state property says that running for the additional $r$ steps leaves the configuration unchanged. The iterate decomposition for runs (`Turing.MultiTapeTM.runFrom_add`) would then make the configuration at time $T$ equal to the one at time $j$, so its state would be $q_a$, contradicting the assumed halted state at time $T$. Now apply the run-agreement result (`Complexity.enumCont_agree_run`) through time $T$: the stop-machine run avoids $q_a$ at every earlier time, so each transition used before time $T$ is shared by the two machines. This gives equality of their configurations at time $T$. Applying the same agreement result through each $j\le T$ gives equality at time $j$ as well; the previously established avoidance for the stop-machine run therefore implies avoidance for the original run.

**Key facts.** `Turing.MultiTapeTM.runFrom_add`, `Complexity.enumCont_absorb`, `Complexity.enumCont_agree_run`.
