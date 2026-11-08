<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.mealyRun_induction -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Induction for Mealy runs

**Claim.** If a property holds for the run on every empty input and is preserved when a first symbol and its transition are prepended, then it holds for every Mealy run.

**Proof.** Induct on the input list, generalizing the starting state. For the empty list, the run is $(a,[])$, so the base assumption applies. For an input $\gamma::l$, let the first transition send state $a$ to its successor state and emit its output symbol. By induction, the property holds for the run on $l$ from that successor state. The preservation assumption then gives the property for the full input and its run, whose output begins with the emitted symbol.
