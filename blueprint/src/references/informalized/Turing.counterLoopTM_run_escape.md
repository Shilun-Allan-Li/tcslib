<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/CounterLoop.lean :: Turing.counterLoopTM_run_escape -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Counter loop escape run

**Claim.** Under the stated round, exit, and initial counter-tape hypotheses, the counter-loop machine reaches its escape configuration at the prescribed time. Before then it is neither done nor escape; throughout the run the counter head stays in the stated interval, and the original tape heads match those of an appropriate round configuration of the simulated machine.

**Proof.** First consider the version of the result that runs the counter loop through an alphabet embedding. The escape-run theorem for that construction (`counterLoopTMVia_run_escape`) gives the endpoint configuration, the absence of done and escape states at earlier times, the counter-head interval bound, and the correspondence of the original tape heads with a round configuration. Specialize this result to the identity embedding on Boolean symbols; the initial tape hypothesis then has exactly the required form, and the identity embedding leaves the counter words unchanged. It remains to transfer the run from the embedded machine to the stated counter-loop machine. The machines agree on every state (`counter_refl_agree`), so the run-equality principle for machines agreeing on all states (`MultiTapeTM.runFrom_eq_of_agreeOn`) shows that their configurations coincide at every time. Substituting these equal runs into the four conclusions gives the claim.

**Key facts.** `Turing.counter_refl_agree`, `Turing.MultiTapeTM.runFrom_eq_of_agreeOn`, `Turing.counterLoopTMVia_run_escape`.
