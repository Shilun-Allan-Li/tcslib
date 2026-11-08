<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/StepBlock.lean :: Turing.StepBlock.readActions_length -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Length of the Transition-Action List

**Claim.** For a fixed state, the list formed by listing transition actions for each of the three possible input reads and all work-tape read patterns has length $3^{k+1}$.

**Proof.** For each fixed input read, mapping the transition function over the work-read patterns preserves the number of entries. The work-read list has length $3^k$ (`Turing.StepBlock.length_workReadsK`), so each of the three blocks has that length. Concatenating the three blocks gives length $3\cdot 3^k=3^{k+1}$.

**Key facts.** `Turing.StepBlock.length_workReadsK`.
