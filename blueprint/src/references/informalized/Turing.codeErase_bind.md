<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/CodeParser.lean :: Turing.codeErase_bind -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bind and Suffix Erasure

**Claim.** Binding a continuation applied to the suffix of an optional value-and-suffix result is the same as first discarding the value and then binding the continuation.

**Proof.** There are two cases. If the initial optional result is failure, both expressions are failure. If it contains a pair consisting of a value and a suffix, both expressions apply the continuation to that same suffix. Thus they agree.
