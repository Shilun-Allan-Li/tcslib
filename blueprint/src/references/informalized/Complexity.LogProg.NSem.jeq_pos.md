<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/NARMKit.lean :: Complexity.LogProg.NSem.jeq_pos -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Preservation Across a True Register Equality Test

**Claim.** If an equality test at a live state takes its positive branch because the two tested register values are equal, and the positive-branch configuration terminates under the guard and accepts exactly when $P$ holds, then, provided the original configuration satisfies the guard, the original configuration has those same properties.

**Proof.** Equality of the register values makes the test's condition true, so executing the deterministic test takes the positive branch and leaves the register valuation and answer unchanged. Apply preservation across a deterministic instruction (\texttt{NSem.det}) to the assumed semantics of that positive-branch configuration and the guard at the original configuration. The executed successor is exactly the assumed positive-branch configuration, giving the desired termination and acceptance equivalence.

**Key facts.** `Complexity.LogProg.NSem.det`.
