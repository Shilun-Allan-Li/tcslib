<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Light/Calls.lean :: Light.Meets.append -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Appending a Program Preserves a Call Bound

**Claim.** If a call in P can execute within cost T and produce an output and final memory satisfying R, then the same call in P followed by P' can do so as well.

**Proof.** Unpack the witness for the original call: it supplies a body at position p in P and an execution of that body with the required cost bound and postcondition. The body remains at position p after appending P' (`Light.getElem?_append_of_eq_some`). The execution and its cost and postcondition are preserved when the program is appended (`Light.Ends.append`). These witnesses establish the claimed call bound for the concatenated program.

**Key facts.** `Light.getElem?_append_of_eq_some`, `Light.Ends.append`.
