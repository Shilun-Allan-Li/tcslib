<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/StepBlock.lean :: Turing.StepBlock.mirror_ne_table -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Original and Table Tape Distinctness

**Claim.** For each $i\in\{0,\ldots,k-1\}$, the tape indexed by $i$ among the original tapes differs from the additional table tape.

**Proof.** The embedded original index has value $i<k$. The table tape has value $k$. These values cannot be equal, so the two finite tape indices are distinct.
