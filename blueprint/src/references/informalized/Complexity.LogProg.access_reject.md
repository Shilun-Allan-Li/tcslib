<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/InputAccess.lean :: Complexity.LogProg.access_reject -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Rejecting After Restoration

**Claim.** If the transition from $st$ moves tape $2$ one cell left and enters the restoring state with no equality result, then the machine has a safe path to the rejecting answer with the first counter reset to zero.

**Proof.** The starting configuration is safe by the standard safety bound for these encoded counters (`Complexity.LogProg.accessCfg_safe`). The one-step path property (`Complexity.LogProg.access_step`) applies the assumed transition. Moving tape $2$ left changes its head from $0$ to $-1$, leaving the other data fixed (`Complexity.LogProg.access_move`). From the restoring state with no equality result, the return procedure restores the first counter to zero and reaches the rejecting answer; its bounds are supplied by $i,k\le |y|+1$ and the bit-length condition on the restoration head (`Complexity.LogProg.access_return`). Concatenating the initial step with this return path proves the claim.

**Key facts.** `Complexity.LogProg.accessCfg_safe`, `Complexity.LogProg.access_step`, `Complexity.LogProg.access_move`, `Complexity.LogProg.access_return`.
