<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Robustness/AlphabetReduction.lean :: Turing.FinTM.arTM_position_visited -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Simulator head positions lie in encoded blocks

**Claim.** For every simulator time $t$ and work tape $i$, its head position is $(N+1)$ times a source head position at some time $s\le t+1$, plus an offset $j\le N+1$.

**Proof.** The run-phase lemma (`arSpacePhase_run`) gives a source time $s\le t$ and says that the simulator configuration at time $t$ is either the encoding of that source configuration or one of its reading, writing, or moving phases. In the encoded case, the head is at the block's initial offset, so take $j=0$. In the reading and writing cases, the phase definitions place the head at the block base plus the phase index; the index bound gives $j\le N+1$. In the moving case, the moving-phase position lemma (`arMoveCfg_position`) gives one of two possibilities: the head is at an offset within the block of the current source head position, or within a block based at the head position after the source action. In the latter case, the source successor-run identity (`runFrom_succ_eq_step'`) identifies that position with the source run at time $s+1$; this time is at most $t+1$. Either way, the resulting block base and offset have the required form.

**Key facts.** `Turing.FinTM.arSpacePhase_run`, `Turing.FinTM.arMoveCfg_position`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`.
