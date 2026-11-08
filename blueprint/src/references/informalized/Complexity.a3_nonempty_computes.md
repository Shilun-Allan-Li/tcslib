<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/EXP.lean :: Complexity.a3_nonempty_computes -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Guarded Computation on Nonempty Input

**Claim.** If $M$ computes $y$ from a nonempty Boolean input $x$ within $t$ steps, then the machine guarding against empty input computes $y$ from $x$ within $t+1$ steps.

**Proof.** Because $x$ is nonempty, its first input symbol is present. The guard’s initial transition therefore emits no output and moves into the renamed initial state of $M$, leaving the tape contents, heads, and input position unchanged. In configuration notation, this first step is the state-renamed initial configuration of $M$ (`moveInputPos_zero`). The run-preservation lemma then identifies the guard’s next $t$ steps with the run of $M$ for $t$ steps, with every state renamed (`a3_nonempty_run`). Finally, computation within a given time is characterized by the run being halted with the specified output (`computesInTime_iff`). Applying that characterization to the computation by $M$ transfers both the halting state and output to the guard’s run, proving computation within $t+1$ steps.

**Key facts.** `Turing.MultiTapeTM.runFrom_succ_eq_step`, `Complexity.a3_nonempty_run`, `Turing.FinTM.computesInTime_iff`, `Turing.moveInputPos_zero`.
