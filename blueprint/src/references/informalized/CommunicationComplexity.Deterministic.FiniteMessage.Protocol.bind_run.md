<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/DeterministicCC/DetComposition.lean :: CommunicationComplexity.Deterministic.FiniteMessage.Protocol.bind_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Execution of a sequential composition

**Claim.** Running a protocol bound to continuations gives the same output as first running the original protocol and then running the continuation selected by its output, on the same inputs.

**Proof.** Proceed by induction on the original protocol. If it outputs $a$ immediately, binding selects $q(a)$, and the original run returns $a$, so both sides are the run of $q(a)$ on the given inputs. If Alice sends a message, her message is determined by the first input. Both the bound protocol and the original protocol therefore follow the same branch, indexed by that message. Apply the induction hypothesis to that branch to identify the remaining execution with the continuation selected by the original protocol's output. If Bob sends a message, the same reasoning applies with his message determined by the second input. This proves the equality in every case.
