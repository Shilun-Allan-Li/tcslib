<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Primitives.lean :: Turing.FinTM.splitPrepare_extra -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Preparation scan completion

**Claim.** One step from the preparation scan configuration at count $|s|$ reaches the ready configuration in phase $1$, with work-head displacement $|s|-1$.

**Proof.** At scan count $|s|$, the scratch-tape head is on the first blank cell of its unary tape. The preparation transition writes a $1$ there, moves that head one cell left, and enters phase $1$; the other work head also moves left. The tape update is exactly the identity that writing at position $q$ extends the unary tape from length $q$ to length $q+1$ (`catalogPolyTape_write`). The input head does not move (`moveInputPos_zero`), and the remaining configuration fields agree directly with the ready configuration.

**Key facts.** `Turing.FinTM.catalogPolyTape_write`, `Turing.moveInputPos_zero`.
