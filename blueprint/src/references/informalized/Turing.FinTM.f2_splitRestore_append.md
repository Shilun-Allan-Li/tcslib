<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_splitRestore_append -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Restoration Append Step

**Claim.** For every natural number $k$ and Boolean words $w,s$, one step of the split-restoration machine from its scan configuration at position $|s|$ yields the clean configuration with state $(1,\mathrm{false})$, input head at $\min(|s|,|w|)+1$, first work tape storing $s$ with true appended if $|s|\le |w|$ and otherwise storing $s$, all other work tapes blank, and all work-tape heads at $|s|-1$.

**Proof.** At scan position $|s|$, the first work-tape head reads blank. Split into the two possible length comparisons. If $|s|\le |w|$, the comparison flag is false, so the transition writes true at cell $|s|$ on the first tape and erases that cell from the scratch tape. The buffer-tape append identity (`bufferTape_append`) identifies the updated first tape with $s$ followed by true; the scratch-tape erasure identity (`f2_splitScratch_erase`) shows that the other tapes become blank. If $|s|>|w|$, the flag is true, so the transition leaves the first tape unchanged and likewise erases the scratch cell at $|s|$; the same erasure identity gives blank other tapes. In both cases the transition enters state $(1,\mathrm{false})$, leaves the input head fixed by zero movement (`moveInputPos_zero`), and moves each work-tape head one place left to $|s|-1$. The output stays empty.

**Key facts.** `Turing.FinTM.bufferTape_append`, `Turing.FinTM.f2_splitScratch_erase`, `Turing.moveInputPos_zero`.
