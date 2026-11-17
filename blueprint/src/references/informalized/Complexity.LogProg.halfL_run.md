<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/Frag.lean :: Complexity.LogProg.halfL_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Register halving run

**Claim.** Under the specified transition and non-call-state hypotheses, deleting the bit of $w$ at position $k$ and placing the head at $k-1$ leads after $k+1$ steps to the tail of $w$ with head at zero; at every earlier time the run remains in a non-call state with head between $-1$ and $k-1$.

**Proof.** Induct on $k$, for all words of length at least $k$. At $k=0$, the erased word is empty and the initial head is at $-1$, where the tape is blank. The prescribed halving transition therefore advances to `next` and moves the head to zero; the initial configuration supplies the sole earlier-time bound.

For the successor step, the word has a bit at position $k$. The starting head is at $k$, which is the end of the prefix of length $k$; the first transition reads that bit and moves left to $k-1$. The resulting state is the halving state determined by the bit just read, and the tape now contains the word with that bit deleted. To see this tape identity, split into the cases where there is a following bit and where the deleted bit was last: updating the next cell gives the shifted suffix in the former case, while erasing the final cell gives the prefix in the latter. The register-action rule (`apply_regAct`), together with the register-read identity (`regCfg_read`) and the one-step run rule (`rrun_one_reg`), verifies this transition. The induction hypothesis now applies to the shortened computation, which takes $k+1$ further steps and ends with the tail of $w$ at head zero. The run concatenation laws (`rrun_succ_left` and `rrun_add`) combine the initial step with that remainder and carry the intermediate-time assertions along: time zero is the original configuration, and every later time before completion is one of the induction-hypothesis times, with its head bound adjusted from $k-1$ to the required $k$.

**Key facts.** `Complexity.LogProg.apply_regAct`, `Complexity.LogProg.regCfg_read`, `Complexity.LogProg.rrun_one_reg`, `Complexity.LogProg.rrun_succ_left`, `Complexity.LogProg.update_bufferTape_cons`, `Complexity.LogProg.bufferTape_erase_last`, `Complexity.LogProg.rrun_add`.
