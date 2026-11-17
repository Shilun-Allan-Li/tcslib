<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/SpaceAmplifyPolyRun.lean :: Randomized.PolyAmp.ps_fin -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Final test semantics

**Claim.** The final-test configuration has probability one exactly when the specified decision rule holds, and probability zero otherwise.

**Proof.** First the initialization bounds ensure every register is at most $B$ (`mk_le`). If $os$ is true, the final label tests whether the accepting count is zero. When the count is zero the routine rejects, and when it is positive it accepts; the deterministic zero-test semantics (`PSem.jz_pos`, `PSem.jz_neg`) together with the semantics of the two terminal labels (`PSem.rej`, `PSem.acc`) give the result, with the output probability identified with the decision rule by `PSem.congr`. If $os$ is false, the routine compares the count against the threshold by adding twice the count to a scratch register and then comparing against $K+1$. The add-twice routine (`psem_addTwice`) reduces this to the comparison loop, whose reachability theorem (`le_loop`) sets the comparison register to the minimum of twice the count and $K+1$, and selects rejection or acceptance according to the threshold comparison. The updated register remains bounded by $B$ (`register_update_le`). The reachability path can therefore be used to transport terminal semantics back to the final label (`AReach.mono`, `PSem.of_reach`); the terminal probabilities and the equivalence with the decision rule again follow from `PSem.rej`, `PSem.acc`, and `PSem.congr`.

**Key facts.** `Randomized.PolyAmp.mk_le`, `Complexity.LogProg.PSem.jz_pos`, `Complexity.LogProg.PSem.rej`, `Complexity.LogProg.PSem.jz_neg`, `Complexity.LogProg.PSem.acc`, `Complexity.LogProg.PSem.congr`, `Complexity.LogProg.psem_addTwice`, `Complexity.Codec.le_loop`, `Complexity.LogProg.register_update_le`, `Complexity.LogProg.AReach.mono`, `Complexity.LogProg.PSem.of_reach`.
