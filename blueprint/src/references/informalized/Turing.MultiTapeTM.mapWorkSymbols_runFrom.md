<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/CounterLoop.lean :: Turing.MultiTapeTM.mapWorkSymbols_runFrom -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Relabelling Commutes with a Run

**Claim.** Relabelling work-tape symbols by a bijection commutes with running the machine for any finite number of steps, provided both the machine and starting configuration are relabelled accordingly.

**Proof.** Take the configuration map that relabels each work-tape symbol by $e$. The one-step compatibility result (`Turing.counter_work_step`) says that stepping the relabelled machine from the relabelled configuration gives the relabelling of the original one-step result. Iterating this compatibility for $t$ steps gives the result: the general run-commutation principle (`Turing.MultiTapeTM.runFrom_comm_of_step`) states that any map commuting with one step also commutes with every finite run. Apply it to this configuration map and the one-step identity just noted.

**Key facts.** `Turing.MultiTapeTM.runFrom_comm_of_step`, `Turing.counter_work_step`.
