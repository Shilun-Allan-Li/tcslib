<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.compareTM_spaceUsedByTape -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Space Used by the Comparison Machine

**Claim.** By any time $t$, each of the two compared tapes has visited at most $\min(|w(fst)|,|w(snd)|)+2$ distinct cells, and each other tape has visited exactly one cell.

**Proof.** Choose the first stopping index $\delta$ for the two words as in the stopping-index lemma; it satisfies $\delta\le\min(|w(fst)|,|w(snd)|)$ (`Turing.catalog_compare_stop`). The comparison-trace lemma describes the head positions throughout the run (`Turing.catalog_compare_trace`). In that trace, every head position on any tape lies between $-1$ and $\delta$, relative to its initial position. The general space bound says that if a tape's head always stays in this interval, then it visits at most $\delta+2$ distinct cells (`Turing.catalog_space_bound`). This applies in particular to each compared tape, and the bound on $\delta$ gives the claimed estimate. For any other tape the trace keeps its head at its initial position at every time, so the constant-position space lemma gives exactly one visited cell (`Turing.catalog_space_one`).

**Key facts.** `Turing.catalog_compare_stop`, `Turing.catalog_compare_trace`, `Turing.catalog_space_bound`, `Turing.catalog_space_one`.
