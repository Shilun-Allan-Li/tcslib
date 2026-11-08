<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/SpaceAmplifyPolyRun.lean :: Randomized.PolyAmp.ps_cp -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Copy operation semantics

**Claim.** If the initial register tuple is bounded, its scratch register is zero, and the source-plus-destination value stays within the bound, then the specified updated tuple inherits the probabilistic semantics at the copy operation's exit label when started at its initial label.

**Proof.** The copy routine repeatedly transfers one unit from the source register to the destination, using the zero scratch register to record progress, until the source is exhausted. The copy-run theorem (`copy_run`) establishes a deterministic reachability path from the initial copy label to its exit label, with the destination replaced by the sum of its old value and the source value. The stated coordinate bounds and sum bound ensure that every register along this path remains within $B$, so the reachability also holds for the register-bound guard. Since the updated tuple at the exit label has probabilistic semantics by hypothesis, semantics can be transported backward along this reachable path (`PSem.of_reach`). The guard conversion is justified by monotonicity of reachability under weakening the guard (`AReach.mono`), using that the register-bound guard follows from the program's bounded-register guard.

**Key facts.** `Complexity.LogProg.copy_run`, `Complexity.LogProg.AReach.mono`, `Complexity.LogProg.PSem.of_reach`, `Randomized.PolyAmp.Reg.le_v`.
