<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Nondeterminism.lean :: Complexity.cont_suffix_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Run After Copying the Suffix

**Claim.** When $y=\mathrm{pre}\,u$, the specified loader run halts and outputs the single bit recording whether $N$ on $x$ with choice word $u$ halts with output $[1]$.

**Proof.** Use the suffix-copying result (`Complexity.cont_copy_run`) for the suffix $u$: after $|u|$ steps, the loader has copied $u$ into the choice buffer and placed the physical input head at the end of $y$. The remaining time splits into the core-entry time and another $|u|+1$ steps by the run-composition law (`Turing.MultiTapeTM.runFrom_add`). The core-entry result (`Complexity.cont_start_core`) puts the machine into the state-renamed simulation-core configuration for the initial configuration of $N$ on $x$, with choice word $u$. The core simulation result (`Complexity.cont_core_run`) identifies the subsequent run with the run of the core itself. The initial-tag fact (`Complexity.choiceCore_initial_tag`) supplies the virtual boundary condition needed by its timed correctness theorem (`Complexity.choiceCore_timed`). That theorem says the core halts and emits exactly the bit testing whether the original run under choices $u$ halts with output $[1]$. Renaming its halting state through the state embedding preserves halting, and its output is unchanged, proving both conclusions.

**Key facts.** `Complexity.cont_copy_run`, `Turing.MultiTapeTM.runFrom_add`, `Complexity.cont_start_core`, `Complexity.cont_core_run`, `Complexity.choiceCore_initial_tag`, `Complexity.choiceCore_timed`.
