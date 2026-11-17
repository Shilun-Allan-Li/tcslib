<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/BiasedThresholdPhenomena.lean :: FABL.shapleyExpectation_eq_uniform_cardinality_then_subset -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Expectation by Cardinality and Subset

**Claim.** For any real-valued function on subsets of an $n$-element set, its Shapley expectation equals the expectation obtained by first choosing a cardinality uniformly from $0,1,\ldots,n$ and then choosing uniformly among subsets of that cardinality.

**Proof.** The Shapley subset distribution is defined as a bind: first sample a cardinality uniformly from $\{0,1,\ldots,n\}$, then sample a subset uniformly from the corresponding cardinality layer. Unfolding the definition of Shapley expectation, the expectation of the function under this bound distribution is the iterated expectation under those two sampling steps, by the expectation-of-a-bind identity (`FABL.pmfExpectation_bind`). The nonemptiness of each cardinality layer ensures the conditional uniform distributions are defined.

**Key facts.** `FABL.pmfExpectation_bind`.
