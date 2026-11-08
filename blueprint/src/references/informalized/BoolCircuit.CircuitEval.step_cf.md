<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/CircuitEvalMachine.lean :: BoolCircuit.CircuitEval.step_cf -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One-Step Configuration Update

**Claim.** If the transition on the scanned input symbol and the two scanned work-tape symbols equals the action encoded by $a$ with input movement $i$, one machine step has the state, clamped input-head movement, tape writes, work-head movement, and output update prescribed by that action.

**Proof.** The configuration is in state $q$, so the machine's step applies its transition to the stated scanned symbols. By the hypothesis, this transition is the action encoded by $a$ with input movement $i$. Applying that action gives its successor state, moves the input head as prescribed, updates each work tape at the common scanned position according to its write instruction, moves both work heads by the action's work-head movement, and appends its optional output symbol. These are precisely the components of the asserted resulting configuration.
