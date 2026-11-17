<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/CircuitEvalMachine.lean :: BoolCircuit.CircuitEval.absStep_none -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Outcome on an absent symbol

**Claim.** For every abstract evaluation state, processing an absent symbol produces a Boolean outcome rather than another state.

**Proof.** Write the state by its phase, values, marked indices, and position, then inspect the possible phases. With an absent input symbol, the transition table either rejects directly or enters the separator-rewind phase; in the latter case the absent work symbol sends it to the copy phase, which also rejects on an absent input. In every case the resulting abstract step is a Boolean outcome, so some Boolean $v$ satisfies the claim.
