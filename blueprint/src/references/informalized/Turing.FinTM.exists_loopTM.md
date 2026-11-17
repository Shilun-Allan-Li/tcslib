<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Loop.lean :: Turing.FinTM.exists_loopTM -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Decision by a bounded loop machine

**Claim.** Under the stated hypotheses, a finite Turing machine outputs the one-bit word indicating whether any iterate through index $R(|x|)$ satisfies the acceptance predicate, within $c(T(n)+1)(R(n)+2)$ steps.

**Proof.** The configuration-loop construction (`Turing.FinTM.exists_loopCfgTM`) gives a finite machine whose successive segments represent the iterates of the state update. Each segment either halts with output $[\mathrm{true}]$ when its acceptance test succeeds or moves to the next segment; the final configuration is halted with the designated negative output. The bounded halted-run lemma (`Turing.FinTM.loop_halted_run`) combines these segments and proves that the resulting output is the one-bit encoding of whether any of the first $R(|x|)+1$ tests accepts, using at most $(R(|x|)+1)c(T(|x|)+1)$ further steps. Including startup, the run-addition law (`Turing.MultiTapeTM.runFrom_add`) gives a total time at most $c(T(|x|)+1)+(R(|x|)+1)c(T(|x|)+1)=c(T(|x|)+1)(R(|x|)+2)$. Finally, monotonicity of computation time (`Turing.FinTM.ComputesInTime.mono`) permits stating the bound at this full time allowance.

**Key facts.** `Turing.FinTM.exists_loopCfgTM`, `Turing.FinTM.loop_halted_run`, `Turing.MultiTapeTM.runFrom_add`, `Turing.FinTM.ComputesInTime.mono`.
