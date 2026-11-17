<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.compareTM_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Runtime and Outcome of the Comparison Machine

**Claim.** There is a time $T\le 2\min(|w(fst)|,|w(snd)|)+2$ by which the comparison machine has reached the completed state with the truth value of whether the two work-tape words agree, and it has not reached a completed state earlier.

**Proof.** Apply the stopping-index lemma to $u=w(fst)$ and $v=w(snd)$. It supplies an index $\delta\le\min(|u|,|v|)$ such that the words agree at every earlier position, have no common symbol at position $\delta$, and their symbols (including absence) at $\delta$ agree exactly when the whole words are equal (`Turing.catalog_compare_stop`). The comparison-trace lemma then describes the machine at every time from its initial word configuration in terms of this first stopping index and the forward and rewind phases (`Turing.catalog_compare_trace`). Set $T=2\delta+2$. The trace shows that all times $t<T$ are still outside either completed state, while at $T$ the machine is in the completed state carrying the equality verdict. Since $\delta$ is at most the shorter word length, this $T$ satisfies the stated bound.

**Key facts.** `Turing.catalog_compare_stop`, `Turing.catalog_compare_trace`.
