<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.compareTM_run_ofCfg -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Comparison from a General Configuration

**Claim.** Under the stated tape-content and running-state assumptions, the comparison machine has a first stopping index $\delta$ bounded by the shorter word length; after $2\delta+2$ steps it has changed only its state to the completed equality verdict, has not completed earlier, and its tape heads obey the stated position bounds.

**Proof.** Use the stopping-index lemma for $u$ and $v$ to choose $\delta\le\min(|u|,|v|)$, with agreement at every earlier position, no common symbol at $\delta$, and equality of the two symbols at $\delta$ equivalent to equality of the words (`Turing.catalog_compare_stop`). The comparison-trace lemma applies directly to the given configuration $d$: its hypotheses are precisely the running-state condition and the assumptions describing the two tapes relative to their head positions (`Turing.catalog_compare_trace`). At time $2\delta+2$, the trace is in the completed phase; the condition at $\delta$ makes its verdict exactly the truth value of $u=v$. The trace also leaves every configuration component other than the state unchanged at that time. For earlier times, inspection of the forward and rewind portions of the trace shows that neither completed state has yet been reached. Finally, inspect the head positions in the same trace: on the two compared tapes they stay between the initial position minus one and the initial position plus $\delta$, inclusive; every other tape head stays fixed. These are the three required conclusions.

**Key facts.** `Turing.catalog_compare_stop`, `Turing.catalog_compare_trace`.
