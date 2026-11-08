<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.mealyRun_carry_clear -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# A cleared carry leaves a word unchanged

**Claim.** Starting with carry false, scanning any finite word with the stated carry rule returns carry false and leaves the word unchanged.

**Proof.** Induct on the word. For the empty word the run returns the initial state and empty output. For $\gamma::w$, a false carry selects the rule that outputs false and leaves $\gamma$ unchanged; the carry remains false. The induction hypothesis says the remaining word is also output unchanged and the final carry is false. Combining the first symbol with that unchanged tail proves the claim.
