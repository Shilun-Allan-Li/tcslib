<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/MeyerMachineParse.lean :: Complexity.Meyer.pcfg_reject -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Rejection on a Blank Input Symbol

**Claim.** If the transition rule in state $st$ on a blank input symbol is the rejecting action, then under the stated position and blank-symbol hypotheses, one step from the buffered configuration has no successor state and output $[\mathrm{false}]$.

**Proof.** The buffered-configuration step formula (`pcfg_step`) identifies the transition rule's input as $y[p-1]?$, which is absent by hypothesis. The assumption on the rule therefore replaces this transition by the rejecting action. By the action-on-configuration formula (`tact_idle_apply`), this action keeps the auxiliary tapes idle, has no successor state, and appends its output symbol false to the initially empty output. The resulting output is exactly $[\mathrm{false}]$, as required.

**Key facts.** `Complexity.Meyer.pcfg_step`, `Complexity.Meyer.tact_idle_apply`.
