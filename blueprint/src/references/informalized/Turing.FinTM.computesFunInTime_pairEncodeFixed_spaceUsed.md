<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.computesFunInTime_pairEncodeFixed_spaceUsed -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fixed-prefix pairing with constant space

**Claim.** For every fixed Boolean word $\alpha$, there are a finite Turing machine and a constant that compute the pairing of $\alpha$ with any Boolean input $x$ in linear time and use at most that constant number of work-tape cells at every time.

**Proof.** Form the fixed word $w$ by doubling each bit of $\alpha$ and appending $01$. The fixed-prefix pairing theorem supplies a machine and a constant that output $w$ followed by $x$, in linear time, with the same constant bounding space at every time (`computesFunInTime_prepend_spaceUsed`). Since $w$ is exactly the fixed prefix in the pair encoding, this machine has the claimed output and bounds.

**Key facts.** `Turing.FinTM.computesFunInTime_prepend_spaceUsed`.
