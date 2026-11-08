<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/StepBlock.lean :: Turing.StepBlock.payload_correct -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Correctness of the Action Payload

**Claim.** If the bits in a record are the first $4k+4$ bits of the serialization of an action $a$, decoding the payload gives $a$’s input movement, work-tape actions, and output, with no successor state.

**Proof.** The serialization begins with the fixed-width fields for the input movement, the $k$ work-tape actions, and the output; the successor-state field follows them. Each movement, work-tape action, and output field has length two, so these first fields together have length $2+4k+2=4k+4$. Thus the stated prefix is exactly the fixed portion of the serialization. Appending one false bit gives the serialization of the action with those same fields and with no successor state: its final state code is the one-bit code for absence. The decoder inverts the action serialization on a serialized action followed by any remaining suffix (the decoding fact `Turing.codeReadActionK_append`). Applying that fact here shows that decoding returns precisely the action with the original fixed fields and no successor. The payload takes the decoded action when decoding succeeds, so it has the asserted value.

**Key facts.** `Turing.codeReadActionK_append`.
