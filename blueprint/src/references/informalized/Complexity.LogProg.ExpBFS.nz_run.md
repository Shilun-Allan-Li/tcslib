<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/ExpBFS/Run.lean :: Complexity.LogProg.ExpBFS.nz_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Next Iteration Initialization Run

**Claim.** From the next-iteration initialization instruction, the machine increments $s$ and clears $U,V,w,K,B_s,c,c_1,s_1$, reaching the first copy instruction of the next first search while satisfying the guard at every preceding configuration.

**Proof.** The initialization code first increments $s$, then clears the registers $U,V,w,K,B_s,c,c_1,s_1$ in sequence. The increment is safe because $s+1\le B$; afterward the register bound follows from the original bound and this inequality. Each clearing operation replaces one register by zero, so it preserves the bound on every register. The corresponding one-step run lemmas `inc_step` and `clr_step` establish the guarded reach for each instruction, and their successive endpoints match the next instruction in the listed sequence. The last endpoint is the first copy instruction, with exactly the stated registers reset. The head starts at zero and no instruction in this sequence moves it, so its position remains zero; the memory is likewise unchanged. The final zero-step reach is supplied by reflexivity.

**Key facts.** `Complexity.LogProg.ExpBFS.inc_step`, `Complexity.LogProg.ExpBFS.clr_step`, `Complexity.LogProg.MReach.refl`.
