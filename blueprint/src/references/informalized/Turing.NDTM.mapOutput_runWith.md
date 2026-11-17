<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/NDCombinators.lean :: Turing.NDTM.mapOutput_runWith -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Output Mapping Commutes with a Run

**Claim.** Running the machine with transition outputs mapped by $f$, from a configuration whose output is mapped by $f$, gives the same result as running the original machine and then mapping its output.

**Proof.** Proceed by induction on the choice word $w$, with the starting configuration arbitrary. For the empty word, neither run takes a step, so the claim is immediate. For a word $b::w$, first take the step selected by $b$. The one-step compatibility theorem (`Turing.NDTM.mapOutput_stepWith`) identifies this step in the mapped machine with mapping the output of the corresponding original step. Apply the induction hypothesis to the remaining choices $w$ and that resulting configuration. The recursion rule for a run on a nonempty word (`Turing.NDTM.runWith_cons`) expresses both runs as this first step followed by the run on $w$, yielding the desired equality.

**Key facts.** `Turing.NDTM.runWith_cons`, `Turing.NDTM.mapOutput_stepWith`.
