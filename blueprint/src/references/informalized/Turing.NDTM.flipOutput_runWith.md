<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/PTM.lean :: Turing.NDTM.flipOutput_runWith -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Flipped output after a run

**Claim.** Running the machine with flipped output from a configuration whose output bits have been flipped gives the flipped-output version of the original run's result.

**Proof.** Induct on the choice word, allowing the starting configuration to vary. For the empty word, both sides are the same flipped starting configuration. For a word beginning with $b$, each run consists of a first step under $b$ followed by the run on the remaining choices (Turing.NDTM.runWith_cons). The one-step compatibility theorem says that flipping the starting output before stepping with the flipped machine gives the flipped result of stepping with the original machine (Turing.NDTM.flipOutput_stepWith). The induction hypothesis then identifies the results of the remaining runs, proving the equality for the full word.

**Key facts.** `Turing.NDTM.runWith_cons`, `Turing.NDTM.flipOutput_stepWith`.
