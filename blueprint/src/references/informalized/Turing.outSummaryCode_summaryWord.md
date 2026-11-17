<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/ConfigGraph.lean :: Turing.outSummaryCode_summaryWord -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Decoding Summary Words

**Claim.** For each code $\tau\in\{0,1,2\}$, the output summary of its associated summary word has code $\tau$.

**Proof.** Check the three possible codes. Code $0$ gives the empty word, whose summary is empty and whose code is $0$. Code $1$ gives $[\mathrm{true}]$, whose summary is accept and whose code is $1$. Code $2$ gives $[\mathrm{false}]$, whose summary is dead and whose code is $2$. Thus the summary code recovers $\tau$ in every case.
