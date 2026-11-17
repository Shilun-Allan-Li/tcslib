<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/InputAccess.lean :: Complexity.LogProg.read_run_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Agreement of read-model and machine runs

**Claim.** For every configuration and every natural number of steps, the read model's run with the unique empty oracle agrees with the run of its underlying multi-tape machine.

**Proof.** Proceed by induction on the number of steps. At time $0$ both runs are the initial configuration. For the successor step, express each run as one transition after its run at the preceding time (`rrun_succ`, `runFrom_succ_eq_step'`) and use the induction hypothesis to identify those preceding configurations. If their state is none, both transition systems keep the configuration fixed. If it is a state label, the read model has no call at that label, so its transition is exactly the underlying machine transition. In either case the next configurations agree.

**Key facts.** `Complexity.LogProg.rrun_succ`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`.
