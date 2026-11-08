<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/RunsStayInLimits.lean :: Light.Exec.bounded -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Preservation of bounded states

**Claim.** If every location and memory value in the initial state has absolute value at most the word limit, then execution preserves this bound in the final state.

**Proof.** Induct on the execution derivation. Skip and a false-guard loop leave the state unchanged. For an assignment, the safe expression evaluates to a value bounded in absolute value by the word limit (`Expr.abs_val_le`); updating one location with such a value preserves the bound on all locations (`abs_update_le`), while memory is unchanged. A store is analogous, updating memory with a safe expression value and leaving locations unchanged. For a sequence or a true-guard loop, apply the induction hypotheses successively to the component executions. In a call, the safe arguments and bounded initial state give a bounded call-frame state (`bounded_callFrame`). The induction hypothesis bounds the body’s final state; its returned value at location zero is therefore bounded, so updating the caller’s assigned location preserves boundedness, while the body’s memory remains bounded.

**Key facts.** `Light.Expr.abs_val_le`, `Light.abs_update_le`, `Light.bounded_callFrame`.
