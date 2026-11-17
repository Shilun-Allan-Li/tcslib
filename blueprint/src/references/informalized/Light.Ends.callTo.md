<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Calls.lean :: Light.Ends.callTo -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Call with a List-Based Local Frame

**Claim.** If a procedure execution specification and the argument hypotheses hold for the frame of $l$, then the call storing its return value at position $x$ has a bounded execution whose final state satisfies the postcondition expressed using the frame obtained by setting position $x$ of $l$ to that return value.

**Proof.** The theorem for calls from a procedure specification ( `Light.Ends.callLast`) applies with the initial locals given by $\mathrm{frame}(l)$. For each return value $r$ and final memory $\mu'$ satisfying $R$, its postcondition asks for $Q$ at the state whose locals are $\mathrm{Function.update}(\mathrm{frame}(l),x,r)$. The identity relating an updated frame to a list with one entry set ( `Light.update_frame_setLocal`) identifies these locals with $\mathrm{frame}(\mathrm{setLocal}(l,x,r))$. The assumed postcondition therefore supplies exactly what the call theorem requires.

**Key facts.** `Light.Ends.callLast`, `Light.update_frame_setLocal`.
