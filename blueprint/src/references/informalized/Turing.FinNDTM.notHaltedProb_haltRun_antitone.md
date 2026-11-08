<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/ExpectedTime.lean :: Turing.FinNDTM.notHaltedProb_haltRun_antitone -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Nonhalting probability is antitone

**Claim.** For choice lengths $t\le t'$, the probability that the machine has not halted at length $t'$ is at most that probability at length $t$.

**Proof.** The halting-run result is prefix stable by `Turing.FinNDTM.haltRun_isPrefixStable`. The general probability monotonicity theorem for prefix-stable partial results states that, when $s\le t$, the probability of returning no result at length $t$ is at most the probability of returning no result at length $s$ (`Randomized.notHaltedProb_le_of_le`). Applying it to the halting-run result with $s=t$ and $t=t'$ gives the desired inequality.

**Key facts.** `Turing.FinNDTM.haltRun_isPrefixStable`, `Randomized.notHaltedProb_le_of_le`.
