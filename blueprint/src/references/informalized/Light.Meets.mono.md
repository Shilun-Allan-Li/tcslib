<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Calls.lean :: Light.Meets.mono -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Monotonicity of Call Bounds

**Claim.** If a call meets cost bound $T$ and postcondition $R$, then any larger bound $T'$ and any weaker postcondition $R'$ are also met.

**Proof.** Unpack the witness for the call: it consists of a procedure body, evidence that this is the body assigned to procedure $p$, and an execution of that body from the specified initial state whose cost is at most $T$ and whose final state satisfies $R$. Apply the monotonicity property of executions (`Light.Ends.mono`): the same execution has cost at most $T'$ because $T\le T'$, and its final state satisfies the new postcondition because $R(r,\nu)$ implies $R'(r,\nu)$. Keep the same body and procedure lookup evidence. These witnesses establish the claim.

**Key facts.** `Light.Ends.mono`.
