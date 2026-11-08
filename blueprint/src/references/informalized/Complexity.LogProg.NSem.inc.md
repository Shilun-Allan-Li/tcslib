<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/NARMKit.lean :: Complexity.LogProg.NSem.inc -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Preservation Across Register Increment

**Claim.** If the instruction at a live state increments register $r$ and continues at a new state, and the resulting configuration terminates under the guard and accepts exactly when $P$ holds, then, provided the original configuration satisfies the guard, the original configuration has those same properties.

**Proof.** An increment is a particular deterministic instruction. Executing it advances to the stated new state, increases register $r$ by one, and leaves all other register values unchanged. Apply preservation across a deterministic instruction (\texttt{NSem.det}) using the guard at the original configuration. The successor produced by executing this increment is precisely the configuration whose termination and acceptance semantics are assumed, so those properties hold at the original configuration as well.

**Key facts.** `Complexity.LogProg.NSem.det`.
