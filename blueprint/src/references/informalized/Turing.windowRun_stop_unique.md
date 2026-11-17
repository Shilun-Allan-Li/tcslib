<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/WindowRun.lean :: Turing.windowRun_stop_unique -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Uniqueness of Non-Exhausted Window Runs

**Claim.** For fixed machine, window radius, initial configuration, and auxiliary value, any two windowed runs that both report an outcome other than exhaustion return the same outcome, configuration, and auxiliary value, regardless of their clock bounds.

**Proof.** Induct on the first clock bound $N$. If it is zero, the run necessarily reports exhaustion, contradicting the hypothesis. For a positive first bound, a zero second bound is likewise impossible. With both bounds positive, inspect the initial configuration. If it is halted, each run reports halting immediately with the same returned data. Otherwise, inspect the successor configuration. If it lies in the window, both runs proceed to that same successor and update the auxiliary value in the same way. Their shorter runs are both non-exhausted, so the induction hypothesis makes their results equal. If the successor lies outside the window, both runs report leaving immediately and return the same initial data. These cases establish equality of the complete results.
