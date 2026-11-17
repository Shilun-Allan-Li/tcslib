<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/RandomizedDecisionTreeComplexity.lean :: FABL.RandomizedDecisionTree.inputCost_ofDeterministic -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Cost of a Deterministic Tree

**Claim.** Choosing a deterministic tree with probability one gives, on every input, expected query count equal to that tree's query count.

**Proof.** The randomized tree has a one-point seed space with probability concentrated at its sole point, and its selected tree is the given deterministic tree. The expectation under a point-mass distribution equals the value at that point (`pmfExpectation_pure`), so the expected query count is precisely the deterministic query count on the input.

**Key facts.** `FABL.pmfExpectation_pure`.
