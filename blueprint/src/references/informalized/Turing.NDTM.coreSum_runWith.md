<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/ConfigGraph.lean :: Turing.NDTM.coreSum_runWith -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Core data and output summary under a run

**Claim.** If two configurations have the same state, input-head position, work-tape contents and head positions, and the same output summary, then running both under any choice word preserves equality of this combined data.

**Proof.** Induct on the choice word, allowing both starting configurations to vary. For the empty word, each run returns its starting configuration, so the assumed equality gives the result directly. For a word beginning with $b$, first take one step from each configuration under that same choice. The one-step preservation theorem says that configurations with equal core data and output summary still have equal core data and output summary after this step (Turing.NDTM.coreSum_stepWith). Apply the induction hypothesis to the remaining choices and these two stepped configurations. This yields equality after the entire run.

**Key facts.** `Turing.NDTM.coreSum_stepWith`.
