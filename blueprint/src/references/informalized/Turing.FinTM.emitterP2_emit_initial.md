<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Primitives.lean :: Turing.FinTM.emitterP2_emit_initial -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Initial Emitter Configuration

**Claim.** The emitter's initial configuration agrees with the one-tape seam configuration carrying $s$, on input $w$.

**Proof.** Both configurations have state $0$ and empty output. Their input-head positions agree because the emitter's split position at counter value zero is the seam position $1$. There is only one tape index: on it the emitter stores the buffer for $s$, exactly the buffer used by the one-tape seam configuration. The corresponding head positions are both zero. Hence every configuration component agrees.
