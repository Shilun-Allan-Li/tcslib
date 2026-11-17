<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/ExpectedTime.lean :: Turing.FinNDTM.haltProb_mono -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Monotonicity of Halting-Output Probability

**Claim.** If $t\le t'$, then the probability of halting with output $v$ using a uniformly random length-$t$ choice word is at most the corresponding probability using length-$t'$ choice words.

**Proof.** The halting result is prefix-stable (`Turing.FinNDTM.haltRun_isPrefixStable`), so extending a choice word cannot change a result that has already halted. For prefix-stable results, the probability of obtaining any specified value is nondecreasing with the choice-word length (`Randomized.randProb_eq_some_mono`). Applying this fact to output $v$ and $t\le t'$ gives the asserted inequality.

**Key facts.** `Turing.FinNDTM.haltRun_isPrefixStable`, `Randomized.randProb_eq_some_mono`.
