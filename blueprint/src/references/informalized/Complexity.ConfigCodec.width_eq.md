<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassPSPACE/TQBF.lean :: Complexity.ConfigCodec.width_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Exact configuration width

**Claim.** The configuration encoding has width $2n+4+\mathrm{stateCount}(M)+3(k(2s+1))$, where the state count includes the additional halting state.

**Proof.** Expand the definitions of width, summary offset, work offset, and state offset. This gives the state offset $2n+2$, followed by the state count and $3(k(2s+1))$ work-tape bits, and then two summary bits. Collecting the constants yields $2n+4+\mathrm{stateCount}(M)+3(k(2s+1))$.
