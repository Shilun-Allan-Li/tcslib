<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/DeterministicCC/DetComposition.lean :: CommunicationComplexity.Deterministic.FiniteMessage.Protocol.pi_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Componentwise execution of product protocols

**Claim.** Running the product protocol on input tuples returns, in each coordinate, the output of the corresponding protocol on that coordinate's inputs.

**Proof.** Induct on the number of coordinates. For zero coordinates, both sides are the unique function from the empty index type, so they agree. For the successor case, the construction runs the head protocol on the head inputs, then runs the tail product protocol on the tail inputs and combines the results by placing the head output at the first coordinate. The bind execution rule identifies the first stage's output and the continuation's execution (`bind_run`); input reindexing makes the head and tail stages receive their respective tuple components (`comap_run`); and mapping the tail output applies the stated tuple assembly (`map_run`). The induction hypothesis identifies each tail coordinate with its corresponding component execution. The head coordinate is the output of the head protocol by construction, so the assembled tuple has the claimed value in every coordinate.

**Key facts.** `CommunicationComplexity.Deterministic.FiniteMessage.Protocol.bind_run`, `CommunicationComplexity.Deterministic.FiniteMessage.Protocol.comap_run`, `CommunicationComplexity.Deterministic.FiniteMessage.Protocol.map_run`.
