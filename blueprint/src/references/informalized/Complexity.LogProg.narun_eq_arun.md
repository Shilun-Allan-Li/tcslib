<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/NARM.lean :: Complexity.LogProg.narun_eq_arun -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Agreement with deterministic simulation

**Claim.** Under the assumption that the deterministic simulation encounters no choice instruction during its first $T$ steps, every choice string of length at most $T$ gives the same configuration as the deterministic simulation after that many steps.

**Proof.** We argue by induction on the choice string, allowing both the initial configuration and the time bound to vary. The empty string leaves the initial configuration unchanged, so the result follows immediately. For a nonempty string $b::\sigma$, its length bound implies $T=T'+1$ for some $T'$. At the initial configuration, if the machine is already halted, both one-step transitions leave it unchanged. Otherwise it is at some state $l$. The hypothesis at time zero says that the instruction at $l$ is not a choice instruction. Since the instruction is either deterministic or a choice, it must be deterministic; for a deterministic instruction the nondeterministic step agrees with the deterministic simulation step, by the deterministic-step agreement fact (`nastep_det`). After these first steps, apply the induction hypothesis to the remaining string $\sigma$ and the new configuration. Its required no-choice hypothesis at time $t<T'$ follows from the original one at time $t+1<T'+1$: the deterministic run from the new configuration for $t$ steps is the original run for $t+1$ steps, by the successor law for deterministic runs (`arun_succ`). The remaining string has length at most $T'$, so induction gives equality after all its steps. The recursive run equation for a cons string (`narun_cons`) and the successor law then identify this result with the deterministic run after $|b::\sigma|$ steps.

**Key facts.** `Complexity.LogProg.nastep_det`, `Complexity.LogProg.narun_cons`, `Complexity.LogProg.arun_succ`.
