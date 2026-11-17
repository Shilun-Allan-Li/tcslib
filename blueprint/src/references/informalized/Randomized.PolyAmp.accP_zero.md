<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/SpaceAmplifyPolyCode.lean :: Randomized.PolyAmp.accP_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Zero-Step Acceptance Probability

**Claim.** For a configuration $C$, the probability of acceptance after zero steps is $1$ if $C$ is already accepting and $0$ otherwise.

**Proof.** At zero steps, there is only the empty choice word, and running on it leaves $C$ unchanged. The probability of a predicate that is constant across all choice words is $1$ when the predicate holds and $0$ otherwise (`randProb_const`). For every choice word of length zero, the run therefore accepts exactly when $C$ does; replacing the run predicate by this constant predicate preserves the probability (`randProb_congr`).

**Key facts.** `Randomized.randProb_const`, `Randomized.randProb_congr`.
