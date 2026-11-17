<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_splitBody_restore -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Restoring the split-body configuration

**Claim.** For a finite Boolean Turing machine $M$, a state $a$, and Boolean words $w,s$, the split-body machine, started in the restore scan at index zero, reaches the restore seam with the updated word $s$ after the stated bounded number of steps, without visiting the anchor state.

**Proof.** The restore-scan machine reaches its terminal configuration, with control state $(4,\mathrm{false})$ and tape word $f2\_splitStep(w,s)$, within $2|s|+|w|+5$ steps by the restore-run result (`f2_splitRestore_run`). Embed its states into the restore phase of the split-body machine. The embedding avoids the anchor; before the terminal state, the split-body transitions agree with the restore-scan transitions, and at the terminal state the restore-scan machine is fixed. The simulation-cut lemma (`f2_splitEmbed_cut`) thus gives a possibly earlier endpoint in the embedded terminal state and guarantees that the split-body machine avoids the anchor throughout. Its time bound is at most the restore-scan bound, and its endpoint has precisely the required tape contents and restore state.

**Key facts.** `Turing.FinTM.f2_splitRestore_run`, `Turing.FinTM.f2_splitEmbed_cut`.
