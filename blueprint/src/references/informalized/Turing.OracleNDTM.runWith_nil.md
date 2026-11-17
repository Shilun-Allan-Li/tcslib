<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/OracleNondeterministic.lean :: Turing.OracleNDTM.runWith_nil -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Run on an Empty Choice Sequence

**Claim.** Running on the empty sequence of choice bits leaves the configuration unchanged.

**Proof.** The recursive definition of running on a choice sequence assigns the empty sequence the identity operation: its output is the starting configuration itself.
