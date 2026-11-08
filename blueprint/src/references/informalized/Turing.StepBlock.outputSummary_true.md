<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/StepBlock.lean :: Turing.StepBlock.outputSummary_true -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Characterization of a True Output Summary

**Claim.** The output summary of a finite binary word is the present bit $1$ exactly when the word consists of the single bit $1$.

**Proof.** Check the word by length. The empty word has absent summary. A singleton word has summary equal to its bit, so its summary is present true precisely for the word $[1]$. Any word of length at least two has summary false, and therefore cannot have summary present true. These cases prove both directions.
