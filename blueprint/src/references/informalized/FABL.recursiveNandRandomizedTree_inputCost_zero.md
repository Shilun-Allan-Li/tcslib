<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/RecursiveNANDComposition.lean :: FABL.recursiveNandRandomizedTree_inputCost_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Base-Level Randomized Input Cost

**Claim.** For every input at level zero, the expected query cost of the randomized tree is $1$.

**Proof.** At level zero the seed is deterministic, so the expectation of the query count is just the query count of the unique selected tree (\(\texttt{FABL.pmfExpectation_pure}\)). That tree queries the sole coordinate once and then reaches a leaf. Its query trace therefore has length $1$, independently of the input.

**Key facts.** `FABL.pmfExpectation_pure`.
