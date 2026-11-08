<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Calls.lean :: Light.Ends.callLast -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Call from a Procedure Specification

**Claim.** A procedure specification for $p$, together with a postcondition that holds for every return value and final memory described by that specification, yields a bounded execution of the call that stores the return value in local variable $x$ and satisfies $Q$.

**Proof.** Unpack the procedure specification to obtain its body, the fact that this body is listed at $p$, and a bounded body execution from the frame of the argument values and initial memory. Apply the monotonicity principle for bounded executions ( `Light.Ends.mono`) to replace the body's return-and-memory condition by the assumed postcondition on the state with local variable $x$ updated to the return value. The argument hypothesis identifies the values of the call expressions with the specified argument list and provides their safety. The call construction theorem ( `Light.Ends.call`) then combines that body execution with the procedure lookup and depth hypotheses; the given cost inequality bounds the resulting call cost by $T$.

**Key facts.** `Light.Ends.mono`, `Light.Ends.call`.
