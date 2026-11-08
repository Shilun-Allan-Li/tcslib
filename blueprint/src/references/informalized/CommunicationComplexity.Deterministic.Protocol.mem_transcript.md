<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/DeterministicCC/Transcript.lean :: CommunicationComplexity.Deterministic.Protocol.mem_transcript -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# An input belongs to its transcript set

**Claim.** For every protocol and input pair, that pair belongs to the input set of the transcript produced by executing the protocol on it.

**Proof.** Proceed by structural induction on the protocol. At an output node, the transcript input set is the full input space, so the given pair belongs to it. At an Alice node, the transcript records the bit $f(x)$ and then the transcript obtained by continuing in branch $P(f(x))$. The pair satisfies the first transcript condition by the choice of that bit, and it belongs to the remaining input set by the induction hypothesis for that branch. At a Bob node the same reasoning uses the bit $f(y)$ and the induction hypothesis for branch $P(f(y))$.
