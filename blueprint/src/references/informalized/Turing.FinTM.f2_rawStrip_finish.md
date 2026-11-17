<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_rawStrip_finish -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Raw Strip Completion

**Claim.** For Boolean words $x,a$ and $i\le |x|$, the raw strip machine started in state $2$ with work tape $a$, head at $|a|-1$, and empty output halts after $2(|a|+1)$ steps with output $a$.

**Proof.** Write $m=|a|+1$, so the stated time is $m+m$. The run decomposition law for iterated machine steps (`Turing.MultiTapeTM.runFrom_add`) splits the computation into two runs of length $m$. The rewind result (`Turing.FinTM.f2_rawStrip_rewind`), applied with $j=|a|$, shows that the first run reaches state $3$ with the head at position $0$, leaving the tape and output unchanged. The replay result (`Turing.FinTM.f2_rawStrip_replay`), applied for another $|a|+1$ steps, describes the resulting configuration: the head is at position $|a|+1$ and the output is $a.take (|a|+1)=a$. One further machine step is accounted for by the stated run decomposition and the transition at the end of replay; unfolding that transition shows the machine enters the halting state without changing the output. Thus the final state is halted and the output is $a$.

**Key facts.** `Turing.MultiTapeTM.runFrom_add`, `Turing.FinTM.f2_rawStrip_rewind`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Turing.FinTM.f2_rawStrip_replay`.
