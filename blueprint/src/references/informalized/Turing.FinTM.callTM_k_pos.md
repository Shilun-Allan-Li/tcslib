<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Loop.lean :: Turing.FinTM.callTM_k_pos -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Positive work-tape count

**Claim.** For every Boolean finite-state machine $M$ and Boolean parameter $e$, the call machine formed from $M$ with parameter $e$ has a strictly positive number of work tapes.

**Proof.** By definition, the call machine's work-tape count is one more than the number of work tapes of its source machine. A successor of any natural number is strictly positive, so the claimed count is positive.
