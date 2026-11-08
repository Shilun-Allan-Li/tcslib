<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/DeterministicCC/Subprotocol.lean :: CommunicationComplexity.Deterministic.Protocol.path_exists_of_isSubprotocol -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Paths from Subprotocol Relations

**Claim.** Whenever $s$ is a subprotocol of $p$, there is a subprotocol path from $s$ to $p$.

**Proof.** Induct on the derivation that $s$ is a subprotocol of $p$. In the reflexive case, the path of length zero witnesses the claim. In each of the four branching cases, the induction hypothesis supplies a path from $s$ to the selected child of $p$; prefix that path with the corresponding Alice-false, Alice-true, Bob-false, or Bob-true step. This constructs the required path in every case.
