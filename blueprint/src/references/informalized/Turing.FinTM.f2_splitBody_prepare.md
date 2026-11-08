<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_splitBody_prepare -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Preparation reaches the counting configuration

**Claim.** For a finite Boolean Turing machine $M$, a state $a$, and Boolean words $w,s$, preparation reaches the counting configuration with simulated state $a$, auxiliary tape containing $s$, and empty output, within the stated bound; the anchor state is avoided throughout.

**Proof.** The preparation machine reaches its ready configuration after $2(|s|+1)$ steps, by the preparation-run result (`f2_splitPrepare_run`). The split-body machine simulates this preparation phase through the state embedding that labels each preparation state as a preparation phase. The embedding never gives the anchor state, and the embedded transition rules agree with those of the preparation machine until its stopping state, where the simpler machine remains fixed. The simulation-cut lemma (`f2_splitEmbed_cut`) therefore supplies a time $t\le2(|s|+1)$ at which the split-body machine is in the embedded ready configuration, while avoiding the anchor at all times through $t$. One further transition changes the ready preparation state into the counting state carrying $a$ and the flag. This transition leaves the tapes and input position unchanged, so it produces exactly the stated counting configuration. The resulting endpoint is also not the anchor state, which extends the avoidance claim to time $t+1$.

**Key facts.** `Turing.FinTM.f2_splitEmbed_cut`, `Turing.FinTM.f2_splitPrepare_run`.
