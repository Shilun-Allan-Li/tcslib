<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_timed_branch_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Timed Branch Simulation

**Claim.** For the specified timed conditional machine, running from the configuration encoding the branch machine's configuration for $t$ steps yields the configuration encoding the branch machine's run for $t$ steps, with the auxiliary tapes and stored branch bit unchanged.

**Proof.** Apply the step-commutation principle (`MultiTapeTM.runFrom_comm_of_step`) to the configuration map that embeds a branch-machine configuration into the timed conditional machine's tapes and states while preserving the auxiliary tapes and branch bit. It remains to check one transition. If the branch configuration is halted, both machines remain halted, so the encoded configuration is unchanged. If it has a state, the embedding places that state in the branch portion of the larger state space. The input symbol is preserved, and the branch's work-tape symbols are read from the corresponding block of tapes. The transition of the timed machine on that state is therefore the branch transition, with its action lifted onto the appropriate tape block. The action compatibility facts for adjoining unused tapes on the left and right (`leftCfg_apply` and `rightCfg_apply`) identify this lifted transition with the encoding of the branch machine's next configuration. Thus the map commutes with every step, and the step-commutation principle gives the equality after $t$ steps.

**Key facts.** `Turing.MultiTapeTM.runFrom_comm_of_step`, `Turing.FinTM.leftCfg_apply`, `Turing.FinTM.rightCfg_apply`.
