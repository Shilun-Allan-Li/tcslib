<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/Frag.lean :: Complexity.LogProg.eqB_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Run Through a Binary Register

**Claim.** Under the stated comparison transition and initial tape contents, the machine scans left through the first register to state $l$ with both heads at zero after $n+1$ steps, while each earlier configuration remains at the comparison state with the heads at a common position between $-1$ and $p$.

**Proof.** Induct on $n$. When $n=0$, the hypotheses force $p=-1$. The scanned cell is blank, since the buffer tape has no contents at a negative position. The comparison transition therefore moves both heads right and enters $l$, placing them at zero. The only earlier time is time zero, where both heads are at $p=-1$, as required.

For the successor step, the hypotheses imply that $p$ is a nonnegative integer position $j$ within the stored word. At this cell the tape contains the corresponding bit, so the transition moves both heads one cell left and remains in $e_B$, reaching position $p-1$. Apply the induction hypothesis from that configuration: it takes the remaining $n+1$ steps to reach $l$ with heads at zero, and all its earlier positions lie between $-1$ and $p-1$. The initial time has position $p$; splitting later times into those before and after the first step shows that the entire run's earlier positions lie between $-1$ and $p$. The one-step run formula (`rrun_one_eq`), the formula for reading the first register after repositioning (`eqCfg_read₁`), and the effect of moving both heads together (`apply_mv2Act`) justify the transition calculation. The run concatenation identities `rrun_succ_left` and `rrun_add` join the first step to the inductive run.

**Key facts.** `Complexity.LogProg.rrun_one_eq`, `Complexity.LogProg.eqCfg_read₁`, `Complexity.LogProg.apply_mv2Act`, `Complexity.LogProg.rrun_succ_left`, `Complexity.LogProg.rrun_add`.
