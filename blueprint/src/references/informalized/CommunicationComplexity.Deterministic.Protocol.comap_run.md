<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/DeterministicCC/DetBasic.lean :: CommunicationComplexity.Deterministic.Protocol.comap_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Pull-Back Commutes with Execution

**Claim.** Running a protocol pulled back along $f_X$ and $f_Y$ on $x'$ and $y'$ gives the same output as running the original protocol on $f_X(x')$ and $f_Y(y')$.

**Proof.** Proceed by structural induction on the protocol. For an output node, both executions return its label. At an Alice node, the pulled-back message evaluated at $x'$ is the original message evaluated at $f_X(x')$. Thus both executions follow the same branch; applying the induction hypothesis to that continuation gives equal outputs. At a Bob node, the pulled-back message at $y'$ equals the original message at $f_Y(y')$, so the executions again follow the same branch, and the induction hypothesis finishes the argument.
