<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/RunsStayInLimits.lean :: Light.bounded_callFrame -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bounded state after a call frame

**Claim.** If every location and memory value of a state $\sigma$ is bounded in absolute value by $W$, then placing the values of safe expressions in a frame and retaining $\sigma$'s memory produces a state whose location and memory values are all bounded by $W$.

**Proof.** Each expression in the argument list is safe in $\sigma$, so its value has absolute value at most $W$ by the bound for values of safe expressions (Light.Expr.abs_val_le). Thus every entry of the list of evaluated arguments satisfies the required bound. The frame bound (Light.bounded_frame) then shows that every location in the new state, including the zero-filled positions, is bounded by $W$. Its memory is unchanged, so the original memory bound gives the other part of the conclusion.

**Key facts.** `Light.Expr.abs_val_le`, `Light.bounded_frame`.
