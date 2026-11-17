<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/ExpectedTime.lean :: Turing.FinNDTM.haltRun_eq_none_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Characterizing a Nonhalting Run

**Claim.** The halting-run result is absent exactly when the machine's state after the given choices is not the halting state.

**Proof.** Unfold the halting-run result, which returns the output when the final state is the halting state and returns nothing otherwise. If the final state is the halting state, the result is present, so it cannot equal none; if it is not the halting state, the result is none. These two cases establish both directions of the equivalence.
