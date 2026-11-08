<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/ConfigGraph.lean :: Turing.summaryTag_none -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Identity for an Empty Update

**Claim.** For every $\tau\in\mathrm{Fin}(3)$, appending no symbol to the word representing $\tau$ leaves its summary tag equal to $\tau$.

**Proof.** With no symbol appended, the representative word for $\tau$ remains unchanged. Its summary code is $\tau$, by the representative-word encoding property (`Turing.outSummaryCode_summaryWord`). This is precisely the tag update with the empty option.

**Key facts.** `Turing.outSummaryCode_summaryWord`.
