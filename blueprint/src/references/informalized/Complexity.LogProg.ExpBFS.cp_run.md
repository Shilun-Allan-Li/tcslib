<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/ExpBFS/Run.lean :: Complexity.LogProg.ExpBFS.cp_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Copy Routine Run

**Claim.** Under the stated bounds, zero scratch value, and source-plus-destination capacity, the copy routine has a finite guarded run that leaves memory and the head position unchanged, adds the source value to the destination, and preserves every other register.

**Proof.** The copy site has distinct source and destination registers, and neither is the scratch register (`cp_ne`). Also, the register bound on the state supplies a bound for every register value (`Bd.toV`). Thus the hypotheses of the general copy-loop result (`copy_run`) hold: the scratch register starts at zero, all registers are bounded, and the destination-plus-source sum fits within the bound. That result gives a guarded register run from the first copy phase to the site’s exit, adding the source into the destination while leaving all other registers unchanged. Finally, the run-lifting lemma (`of_areach`) turns this register-only run into a memory-machine run. Its head-position bound is exactly the assumed bound on $p$, and it leaves both the memory and head position fixed, as required.

**Key facts.** `Complexity.LogProg.ExpBFS.St.Bd.toV`, `Complexity.LogProg.ExpBFS.cp_ne`, `Complexity.LogProg.copy_run`, `Complexity.LogProg.ExpBFS.of_areach`.
