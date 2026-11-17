<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassNP/Tautology.lean :: Complexity.taut_verdict -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Verdict Transition

**Claim.** From a verdict state carrying bit $b$, one verifier step halts, outputs the one-bit word $b$, and leaves the input position, work tape, and work-head position unchanged.

**Proof.** In verdict state the transition halts, emits $b$, and makes no input or work-tape movement or modification. Applying this transition to the configuration therefore changes only the state to the halting state and the output from empty to $[b]$, giving the claimed configuration.
