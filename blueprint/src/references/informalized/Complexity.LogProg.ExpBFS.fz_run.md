<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/ExpBFS/Run.lean :: Complexity.LogProg.ExpBFS.fz_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Reset Before the Final Scan

**Claim.** Starting from any state whose registers are all at most $B$, the machine reaches the final-scan preparation state with $U,V,w,K,B_s$ reset to zero, all other registers unchanged, the same memory marking, and head at zero; the guard holds at every time strictly before arrival.

**Proof.** The reset state executes five clear instructions in sequence, clearing $U$, then $V$, then $w$, then $K$, and finally $B_s$. After each clear, the next instruction is the next reset state, with the last leading to the final-scan preparation state. Each clear is justified by the one-step guarded-run property for clearing a register (`clr_step`). The original register bounds imply the bounds after each clearing, and the head remains at zero, which lies between zero and $P$. Chaining the five steps and then using reflexivity at the target configuration (`MReach.refl`) gives the required guarded reachability. The memory marking is unchanged throughout.

**Key facts.** `Complexity.LogProg.ExpBFS.clr_step`, `Complexity.LogProg.MReach.refl`.
