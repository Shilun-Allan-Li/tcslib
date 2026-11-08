<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/ExpectedTime.lean :: Turing.FinNDTM.notHaltedProb_haltRun_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Nonhalting probability at zero steps

**Claim.** At choice length zero, the probability that the machine has not halted is $1$.

**Proof.** At length zero there is only the empty choice word. Its run is the initial configuration, whose state is the initial state and hence is not `none`. Thus its halting-run result is absent. Equivalently, the zero-step instance of the halting criterion (`Turing.FinNDTM.haltRun_eq_none_iff`) identifies absence with a nonhalting state. The event being counted is therefore true for every zero-length choice; replacing it by the always-true event preserves its probability (`Randomized.randProb_congr`), and the probability of the always-true event is $1$ (`Randomized.randProb_true`).

**Key facts.** `Turing.FinNDTM.haltRun_eq_none_iff`, `Randomized.randProb_congr`, `Randomized.randProb_true`.
