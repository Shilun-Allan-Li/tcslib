<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/StepBlock.lean :: Turing.StepBlock.mirror_ne_summary -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Original and Summary Tape Distinctness

**Claim.** For each $i\in\{0,\ldots,k-1\}$, the tape indexed by $i$ among the original tapes differs from the additional summary tape.

**Proof.** The original tape index, embedded into the enlarged index type, has value $i$, while the summary tape has value $k+1$. Since $i<k$, these values differ. Indices in a finite type with different values are unequal, proving the claim.
