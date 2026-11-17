<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/CircuitComplexity/MeyerTableau.lean :: Complexity.Meyer.tabAns_st -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# State Selector Answer

**Claim.** For a state selector, the table answer is true exactly when the configuration's state and summarized output match the selector, independently of the walk count.

**Proof.** Unfold the table answer and the selector-answer function. In the state-selector case, the selector-answer function returns the decision of the conjunction that the configuration's state equals the selected optional state and its output summary equals the selected register value. The input and work-tape symbols, including those obtained after the specified number of walk steps, do not enter this clause. This gives the asserted equality for every walk count.
