<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/StepBlock.lean :: Turing.StepBlock.summary_ne_table -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Distinct Summary and Table Tapes

**Claim.** For every nonnegative integer $k$, the summary tape among $k+2$ tape indices differs from the table tape.

**Proof.** Assume for contradiction that the two indices are equal. Applying the value map to this equality would make their natural-number values equal. By the definitions of the two indices, those values are $k+1$ and $k$, respectively, which are unequal. This contradiction proves they are distinct.
