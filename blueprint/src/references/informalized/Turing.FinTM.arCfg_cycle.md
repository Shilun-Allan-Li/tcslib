<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/AlphabetReduction.lean :: Turing.FinTM.arCfg_cycle -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One simulator cycle

**Claim.** Running the binary block-code simulator for $3(N+1)+2$ steps from the encoding of a configuration $c$ yields the encoding of the configuration after one step of the original machine from $c$.

**Proof.** Split according to whether $c$ is halted. If its state is none, one original step leaves $c$ unchanged, and the encoded configuration is also halted; a halted simulator stays fixed under every number of steps. Suppose instead that $c$ has state $q$. Rewrite the total duration as $(N+1)+\bigl(1+((N+1)+((N+1)+1))\bigr)$ and divide the run into phases. The read phase lemma (`arReadCfg_run`) shows that the first $N+1$ steps place the simulator in the state representing a complete reading of the encoded tape symbols. Its next transition dispatches the original machine's transition on state $q$, the current input symbol, and those decoded tape symbols (`arReadCfg_dispatch`), yielding the corresponding write phase. The write phase lemma (`arWriteCfg_run`) runs that phase for $N+1$ steps, after which the move phase lemma (`arMoveCfg_run`) runs for another $N+1$ steps and reaches the encoding of the configuration obtained by applying the original transition action. These phases, including the dispatch and the final transition, use $3(N+1)+2$ steps in total. The resulting encoded configuration is the encoding of the original machine's next configuration, as claimed.

**Key facts.** `Turing.MultiTapeTM.step_of_halt`, `Turing.MultiTapeTM.runFrom_of_halt`, `Turing.MultiTapeTM.runFrom_add`, `Turing.FinTM.arReadCfg_run`, `Turing.FinTM.arReadCfg_dispatch`, `Turing.FinTM.arWriteCfg_run`, `Turing.FinTM.arMoveCfg_run`.
