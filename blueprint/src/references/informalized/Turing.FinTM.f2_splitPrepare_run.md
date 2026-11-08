<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_splitPrepare_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Preparation Run

**Claim.** For every natural number $k$ and Boolean words $w,s$, running the split-preparation machine on input $w$ from its initial configuration for $2(|s|+1)$ steps yields the specified configuration with state $(2,|w|<|s|)$, input head at $\min(|s|,|w|)+1$, the catalog tape filled through cell $|s|$, all work-tape heads at zero, and empty output.

**Proof.** First identify the initial configuration with the scan configuration at position $0$: the first work tape stores $s$, the other tapes are blank, the input head starts at position $1$, and all work-tape heads are at zero. The scan lemma (`f2_splitPrepare_scan`) then gives the scan configuration at position $|s|$ after $|s|$ steps. One additional step is the extra preparation step (`f2_splitPrepare_extra`), producing the ready configuration in state $1$ with first work-tape head at $|s|-1$. The remaining $|s|+1$ steps are exactly the rewind lemma (`f2_splitPrepare_rewind`) with $j=|s|$, which gives state $2$ and all heads at zero. Splitting $2(|s|+1)$ into these two blocks of $|s|+1$ steps and using the run composition identity (`runFrom_add`) proves the claimed run.

**Key facts.** `Turing.FinTM.f2_splitPrepare_scan`, `Turing.MultiTapeTM.runFrom_succ_eq_step'`, `Turing.FinTM.f2_splitPrepare_extra`, `Turing.MultiTapeTM.runFrom_add`, `Turing.FinTM.f2_splitPrepare_rewind`.
