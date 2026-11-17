<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/ConfigGraph.lean :: Turing.summaryTag_append -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Summary Update by Appending

**Claim.** For every Boolean word $u$ and optional Boolean symbol $b$, the code of the summary of $u$ followed by $b$ equals the summary tag obtained from the code of the summary of $u$ and $b$.

**Proof.** Let $\tau$ be the code of the summary of $u$. By the fact that encoding the representative word for a summary recovers its code (`Turing.outSummaryCode_summaryWord`) and injectivity of summary codes (`Turing.outSummaryCode_injective`), the summary of $u$ equals the summary of the representative word for $\tau$. Appending the same word $b$ preserves this equality of summaries, by the append congruence property (`Turing.outSummary_append_congr`). Thus the summary of $u$ followed by $b$ equals the summary of the representative word for $\tau$ followed by $b$. Applying the summary code to both sides gives the desired equality, since the right side is exactly the tag update defined from $\tau$ and $b$.

**Key facts.** `Turing.outSummaryCode_summaryWord`, `Turing.outSummaryCode_injective`, `Turing.outSummary_append_congr`.
