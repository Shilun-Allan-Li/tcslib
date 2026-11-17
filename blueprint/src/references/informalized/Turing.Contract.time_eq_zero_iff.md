<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Contract/Basic.lean :: Turing.Contract.time_eq_zero_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Zero Running Time and Exit Membership

**Claim.** For a configuration in the contract entry state satisfying its precondition, the contract running time is zero exactly when the entry state belongs to the exit set.

**Proof.** Suppose first that the running time is zero. The contract endpoint is then the configuration at time zero, by the contract's exact-run property and the fact that running for zero steps leaves a configuration unchanged (`Turing.MultiTapeTM.runFrom_zero`). Its state is therefore the initial entry state, and endpoint exit membership gives the desired membership. Conversely, suppose the entry state belongs to the exit set. If the running time were positive, the contract's cut condition would say that the state at time zero is not in the exit set. But the run at time zero is the starting configuration, whose state is the entry state. This contradiction shows the running time is zero.

**Key facts.** `Turing.MultiTapeTM.runFrom_zero`.
