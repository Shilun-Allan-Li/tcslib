<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/NDClockHostRun.lean :: Turing.ClockHost.ReadyAt.next -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Readiness After a Choice-Word Run and Reset

**Claim.** If $a$ is ready at $m$, the input length is at most $m$, and $u$ has length $m$, then running $A$ on $u$ from $a$ and applying the next-attempt reset produces a configuration ready at $m$.

**Proof.** The reset explicitly sets the state to the initial state of $A$ and clears the output. Its input-head position is $1$: the input head is moved left repeatedly by the reset, and the final right move returns it to the initial position, as expressed by the fact that moving right after the prescribed left sweep lands at $1$ (`moveInputPos_inLeft`). It remains to check the blank region of each work tape. During a run of $u$, the head on any tape can move by at most $|u|=m$, by the bound on work-head displacement (`abs_runWith_workTapePos_sub_le`). Consequently, every cell at or beyond the reset head position minus $m$, after the reset's positive shift of $3(m+1)$, corresponds to a cell at or beyond the original head position plus $m$. The run has left such cells unchanged (`runWith_workTapes_of_le`), and readiness says those original cells were blank. Hence all cells required by the readiness condition are blank after the reset.

**Key facts.** `Turing.ClockHost.moveInputPos_inLeft`, `Turing.NDTM.abs_runWith_workTapePos_sub_le`, `Turing.NDTM.runWith_workTapes_of_le`.
