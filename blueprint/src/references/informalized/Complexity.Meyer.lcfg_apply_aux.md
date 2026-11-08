<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/MeyerMachineRun.lean :: Complexity.Meyer.lcfg_apply_aux -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Effect of a lifted action

**Claim.** When the first auxiliary tape is unchanged and its head does not move, applying the lifted action preserves the simulated machine’s work tapes and heads, updates the other two auxiliary tapes and their heads as prescribed, keeps the input-head position $P$, and appends the optional output bit.

**Proof.** The general action-application formula says that an action updates each tape by its specified write and moves each head by its specified displacement, while appending the optional output (`Complexity.Meyer.tact_apply`). Here the ordinary work-tape action is idle, so the simulated work tapes and their head positions are unchanged. On the auxiliary tapes, the first action is also idle by hypothesis; the other two tapes are updated by writing at $z_C$ and $z_O$, when a write is prescribed, and their heads move by the indicated amounts. Finally, the input-head movement is zero, which leaves $P$ fixed (`Turing.moveInputPos_zero`). Substituting these componentwise updates gives exactly the stated configuration.

**Key facts.** `Complexity.Meyer.tact_apply`, `Turing.moveInputPos_zero`.
