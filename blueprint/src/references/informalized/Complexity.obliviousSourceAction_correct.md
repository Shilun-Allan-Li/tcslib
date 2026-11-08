<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/ObliviousCandidate.lean :: Complexity.obliviousSourceAction_correct -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Correctness of the selected source action

**Claim.** At the payload vector centered at offset zero, the action selected from a configuration’s state agrees with the totalized action of the original machine at that configuration.

**Proof.** At offset zero, the payload vector is exactly the vector of symbols read from the configuration (`sourcePayload_origin`). If the configuration state is absent, both action definitions return the stationary action with no writes, output, or successor state. If the state is present, the selected action feeds the virtual input read and each work-tape read to the original transition function; these are precisely the configuration’s scanned input and work-tape symbols. Thus the two actions agree in either state case.

**Key facts.** `Complexity.sourcePayload_origin`.
