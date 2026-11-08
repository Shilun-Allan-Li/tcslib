<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/ExpBFS/Run.lean :: Complexity.LogProg.ExpBFS.stepH_of -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Deterministic Step to Halting Run

**Claim.** If the instruction at the given label is the specified deterministic instruction, then any guarded halting run beginning just after that instruction yields a guarded halting run beginning at the original label with the same registers, memory, and head position.

**Proof.** The bounds on the registers and head position imply that the original configuration satisfies the guard (`g_of`). Apply the one-step extension principle for halting runs (`MHalt.step`): it suffices that the successor configuration has the given guarded halting run. By the instruction equation, executing the deterministic instruction at the original label produces exactly the successor configuration in the hypothesis, with the same tape and head. Hence the original configuration also halts with the same answer while satisfying the guard at every earlier time.

**Key facts.** `Complexity.LogProg.ExpBFS.g_of`, `Complexity.LogProg.MHalt.step`.
