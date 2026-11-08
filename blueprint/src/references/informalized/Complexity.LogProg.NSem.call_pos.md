<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/NARMKit.lean :: Complexity.LogProg.NSem.call_pos -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Semantics of a Positive Oracle Call

**Claim.** If the oracle answers true on the encoded pairing of $x$ with the binary word for register $r$, and the successor at $l_1$ satisfies the termination and acceptance semantics for $P$, then the configuration at $l$ satisfies those semantics as well, provided it satisfies $G$.

**Proof.** Apply the deterministic-step semantics lemma: because the current configuration satisfies $G$, the termination and acceptance semantics at the deterministic successor imply those semantics at the current configuration (`NSem.det`). The virtual word presented by this whole-input call with its single register is exactly the pairing of $x$ with that register's binary word (`vword_whole₁`). The assumed true oracle answer therefore selects the positive branch, making the successor the configuration at $l_1$ as required.

**Key facts.** `Complexity.LogProg.NSem.det`, `Complexity.LogProg.vword_whole₁`.
