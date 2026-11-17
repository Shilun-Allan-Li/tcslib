<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/CircuitEvalRun.lean :: BoolCircuit.CircuitEval.step_rej -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Rejection halts with false output

**Claim.** If the transition from the specified configuration is the rejection action, then after one step the machine is halted and its output is the one-bit string consisting of false.

**Proof.** The one-step run is the machine’s step applied to the initial configuration: the run-at-successor and run-at-zero identities (`Turing.MultiTapeTM.runFrom_succ_eq_step`, `Turing.MultiTapeTM.runFrom_zero`) reduce the claim to describing that step. The transition hypothesis identifies its action as the rejection action, so the configuration-step formula (`BoolCircuit.CircuitEval.step_cf`) gives the resulting state, tape contents, head positions, and output by substituting the rejection action’s fields. Its successor state is absent, and its output contribution is `[false]`; since the initial output is empty, the resulting output is `[] ++ [false] = [false]`. Thus the state is halted and the output has the asserted value.

**Key facts.** `Turing.MultiTapeTM.runFrom_succ_eq_step`, `Turing.MultiTapeTM.runFrom_zero`, `BoolCircuit.CircuitEval.step_cf`.
