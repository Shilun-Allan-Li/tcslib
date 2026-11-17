<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Codec/Run.lean :: Complexity.Codec.cp_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Execution of a Register-Copy Routine

**Claim.** Under the stated register bound and destination-versus-source inequality, the copy routine has a guarded execution to its prescribed continuation, copying the source's initial value into the destination and leaving every other register unchanged.

**Proof.** The routine repeatedly tests whether the destination equals the source. If they differ, it increments the destination and returns to the test; if they agree, it continues to the designated next label. The register-copy loop theorem (`registerCopy_loop`) supplies a guarded execution of this loop with the stated final assignment. Its hypotheses require distinct destination and source registers, which holds for every copy instruction (`cpDst_ne`), and the program equations identify the test, increment, and continuation labels with the loop's required branches. The destination never exceeds the source during the increments, so the assumed register bound is preserved; the theorem also provides the guard condition throughout the execution.

**Key facts.** `Complexity.Codec.cpDst_ne`, `Complexity.LogProg.registerCopy_loop`.
