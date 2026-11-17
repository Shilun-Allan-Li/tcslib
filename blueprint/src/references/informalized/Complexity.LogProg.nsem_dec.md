<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/NARMKit.lean :: Complexity.LogProg.nsem_dec -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Semantics of Decrement

**Claim.** If the successor configuration after decrementing register $r$ has the stated terminating semantics, then so does the configuration before the decrement.

**Proof.** The decrement instruction takes one deterministic step, replacing $v(r)$ by the truncated natural-number difference $v(r)-1$ and leaving the other registers and result unchanged. This is exactly the successor assignment in the hypothesis. The deterministic-step semantics rule (`NSem.det`), together with the guard at the original configuration, transfers termination and acceptance equivalence back across that step.

**Key facts.** `Complexity.LogProg.NSem.det`.
