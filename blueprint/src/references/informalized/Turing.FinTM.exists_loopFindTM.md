<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Loop.lean :: Turing.FinTM.exists_loopFindTM -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Result-bearing bounded loop machine

**Claim.** Under the stated startup, invariant, round, and counter-machine hypotheses, a finite Turing machine outputs the result belonging to the first accepting iterate among indices at most $R(|x|)$, or the empty word if none accepts, within $c(T(n)+1)(R(n)+2)$ steps.

**Proof.** The loop-host construction packages the counter machine and the body machine into a single finite machine and supplies a clean initial configuration followed by a sequence of configurations for the successive invariant states. Its contract lemma (`Turing.FinTM.loopHost_contracts`) ensures that each segment either halts with the prescribed output when that iterate accepts, or advances to the next configuration, and that the final configuration is halted with empty output. Apply the bounded search-run lemma (`Turing.FinTM.loop_find_run`) to these $R(|x|)+1$ segments, each bounded by $c(T(|x|)+1)$ steps. It shows that the run from the first loop configuration halts with the output attached to the least accepting index, or with the empty word if there is no such index. The loop-host startup takes at most $c(T(|x|)+1)$ steps; concatenating startup and the search run is justified by the run-addition law (`Turing.MultiTapeTM.runFrom_add`). Thus the total time is at most $c(T(|x|)+1)+(R(|x|)+1)c(T(|x|)+1)=c(T(|x|)+1)(R(|x|)+2)$. The machine therefore computes the required function within this bound.

**Key facts.** `Turing.FinTM.loopHost_contracts`, `Turing.FinTM.loop_find_run`, `Turing.MultiTapeTM.runFrom_add`, `Turing.FinTM.ComputesInTime.mono`.
