<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/StepBlock.lean :: Turing.StepBlock.outputSummary_append -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Summary of an Appended Output Symbol

**Claim.** For every finite binary word $w$ and optional bit $b$, the summary of $w$ with $b$ appended, when present, is obtained by emitting $b$ into the summary of $w$.

**Proof.** If no bit is appended, the word and its summary are unchanged, matching the rule for emitting no symbol. If a bit is appended, inspect the possible lengths of the original word. For the empty word, the resulting singleton has summary equal to the appended bit. For a singleton original word, the result has length two, so its summary is false. For an original word of length at least two, appending preserves the fact that its length is at least two, and its summary remains false. In each case the result agrees with the definition of updating the summary by the appended bit.
