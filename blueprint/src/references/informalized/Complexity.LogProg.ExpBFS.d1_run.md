<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/ExpBFS/Run.lean :: Complexity.LogProg.ExpBFS.d1_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Register Reset Run

**Claim.** If every field of the register state is at most $B$, the machine reaches the move control state with $U,V,w,K,Bs$ cleared and every other field unchanged, along a guarded run.

**Proof.** The reset routine clears the five designated registers in sequence: first $U$, then $V$, $w$, $K$, and $Bs$. At each step, the appropriate instance of the clear-transition lemma (`clr_step`) supplies a guarded run for that transition. Clearing a register to zero preserves the bound on every field, so the lemma remains applicable at the next control state. The memory and head position stay fixed throughout. Once the fifth clearing transition reaches the move state, reflexive reachability (`MReach.refl`) supplies the remaining zero-length run to the stated endpoint.

**Key facts.** `Complexity.LogProg.ExpBFS.clr_step`, `Complexity.LogProg.MReach.refl`.
