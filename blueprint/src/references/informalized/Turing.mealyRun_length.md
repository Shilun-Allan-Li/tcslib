<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.mealyRun_length -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Mealy Run Length Preservation

**Claim.** For every finite input list, the output produced by running the Mealy machine from any initial state has the same length as the input.

**Proof.** Induct along the run. On the empty input, both the output and input are empty, so their lengths agree. For a nonempty input, the run emits the output of the first transition followed by the output from the recursive run on the remaining input. By induction those latter lengths agree; adding one to each gives the result. This is the stepwise induction principle for Mealy runs (`Turing.mealyRun_induction`).

**Key facts.** `Turing.mealyRun_induction`.
