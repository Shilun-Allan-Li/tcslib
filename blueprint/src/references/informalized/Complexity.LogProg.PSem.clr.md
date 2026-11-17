<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/NARMPSem.lean :: Complexity.LogProg.PSem.clr -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Semantics Under Register Clearing

**Claim.** If the instruction at $l$ deterministically clears register $r$ and moves to $l'$, then semantics from $l'$ with $r$ set to zero implies the same semantics from $l$, provided the guard holds at the initial configuration.

**Proof.** A deterministic instruction preserves semantics from its one-step successor back to the current configuration when the guard holds (`PSem.det`). Clearing register $r$ updates its value to zero and leaves all other registers and the result field unchanged. Thus the successor is exactly the configuration at $l'$ with the updated valuation specified in the hypothesis, and the deterministic-step result applies.

**Key facts.** `Complexity.LogProg.PSem.det`.
