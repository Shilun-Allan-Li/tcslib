<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CookLevin/Hardness.lean :: Complexity.clA5Round -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One Round of the Five-Module Host

**Claim.** Under the clean contracts for modules $E$ and $I$, the five-module host returns to its loop anchor with updated word $\mathrm{next}(w)$ and output $\mathrm{emit}(w)$ within the stated time bound, without visiting the anchor at an intermediate positive time.

**Proof.** The host first takes one dispatch step from the loop anchor to the entry of module 3, the emission module. Its clean contract, applied with identity result map and emission $\mathrm{emit}$, supplies a positive run of length $t_E\le B_E(|w|)$ that reaches module 4's entry, preserves the word, and appends $\mathrm{emit}(w)$ to the output (`Complexity.clA5Host_clean`). Applying the clean contract for module 4 with result map $\mathrm{next}$ and empty emission gives a positive run of length $t_I\le B_I(|w|)$ to the loop anchor, with the updated word and the prior output preserved. The host's tape bank is large enough for each module (`Complexity.clA5Modules_bound`). The guard-combination lemma ensures that neither module run reaches the loop anchor early (`Complexity.clA5_guard_add`). Concatenate the dispatch step and these two runs: the total time is $1+t_E+t_I$, which is positive and at most $1+B_E(|w|)+B_I(|w|)$, and the final configuration has the claimed word and output.

**Key facts.** `Complexity.clA5Modules_bound`, `Complexity.clA5Host_clean`, `Complexity.clA5_guard_add`, `Turing.MultiTapeTM.runFrom_succ_eq_step`, `Turing.MultiTapeTM.runFrom_add`.
