<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/NARMKit.lean :: Complexity.LogProg.NSem.call_neg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Semantics of a Negative Oracle Call

**Claim.** If the oracle answers false on the encoded pairing of $x$ with the binary word for register $r$, and the successor at $l_0$ satisfies the termination and acceptance semantics for $P$, then the configuration at $l$ satisfies those semantics as well, provided it satisfies $G$.

**Proof.** The call instruction is deterministic, so the deterministic-step semantics lemma transfers the successor's termination and acceptance semantics back to the current configuration, provided the current configuration satisfies $G$ (`NSem.det`). It remains to identify the successor of the call: the virtual word for whole-input mode with the single register $r$ is the pairing of $x$ and that register's binary word (`vword_whole₁`). By the assumed false oracle answer, the call takes its negative branch, so this deterministic successor is precisely the configuration at $l_0$.

**Key facts.** `Complexity.LogProg.NSem.det`, `Complexity.LogProg.vword_whole₁`.
