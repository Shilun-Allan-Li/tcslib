<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clBank_idle -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fixed Returned Bank Configuration

**Claim.** Any bank configuration whose every component is in the return state is unchanged by one bank step.

**Proof.** Unfold the bank step and use the hypothesis that its control is the constant function with value the return state. In that state the counter machine takes its stationary control action: it makes no work-tape writes or head movements, emits no output, and leaves each component in the return state. The bank's input-head movement is zero, so its input position is unchanged by the zero-movement identity (`Turing.moveInputPos_zero`). Its work tapes, work-head positions, and output are therefore unchanged as well; its control is unchanged by the hypothesis. Equality of all configuration fields gives the result.

**Key facts.** `Turing.moveInputPos_zero`.
