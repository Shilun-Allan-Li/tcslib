<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/CounterLoop.lean :: Turing.counterLoopTM_run_done -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Boolean Counter Loop Completion

**Claim.** For a Boolean-tape machine satisfying the stated round conditions, the counter-loop machine reaches its done configuration at time $T$, with the extra tape true across the word cells. Before $T$ its state is neither done nor escape; through $T$ the extra head remains in the stated interval and the first $k$ head positions match the corresponding round runs.

**Proof.** First compare the Boolean counter-loop machine with the symbol-encoded construction using the identity embedding of Boolean symbols. The agreement theorem `Turing.counter_refl_agree` says these machines agree on all states, so `Turing.MultiTapeTM.runFrom_eq_of_agreeOn` identifies their runs at every time. The initial buffer hypothesis translates directly to the encoded-buffer hypothesis. Now apply `Turing.counterLoopTMVia_run_done` to the encoded machine. Its conclusion supplies the endpoint, state exclusions, and head-position properties; replacing encoded Boolean symbols by the identity embedding recovers exactly the Boolean-machine conclusion.

**Key facts.** `Turing.MultiTapeTM.runFrom_eq_of_agreeOn`, `Turing.counterLoopTMVia_run_done`, `Turing.counter_refl_agree`.
