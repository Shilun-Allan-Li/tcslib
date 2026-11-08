<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/ConfigGraph.lean :: Turing.outSummaryCode_injective -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Injectivity of the Summary Code

**Claim.** The map assigning a code in $\{0,1,2\}$ to each output-summary value is injective.

**Proof.** Take two output-summary values with the same code. Since there are only three possibilities—empty, accept, and dead—compare the two values case by case. Their codes are respectively $0$, $1$, and $2$, which are distinct, so equality of codes forces the two values to be the same.
