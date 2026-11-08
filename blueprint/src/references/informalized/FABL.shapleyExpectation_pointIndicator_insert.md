<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/BiasedThresholdPhenomena.lean :: FABL.shapleyExpectation_pointIndicator_insert -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Inserted-Set Indicator Expectation

**Claim.** The Shapley expectation of the indicator that inserting $i$ into the sampled subset gives $A$ is the sum of the probabilities of $A$ and $A\setminus\{i\}$ if $i\in A$, and is zero if $i\notin A$.

**Proof.** Expand the expectation as a sum over sampled subsets. If $i\notin A$, inserting $i$ always produces a set containing $i$, so it cannot equal $A$ and every term vanishes. If $i\in A$, the characterization of an insertion equaling $A$ (`FABL.insert_eq_fixed_iff`) says that the sampled subset must be either $A$ or $A\setminus\{i\}$. Restricting the sum to these two subsets leaves their probabilities, since both corresponding indicators equal one. This is the claimed expression.

**Key facts.** `FABL.insert_eq_fixed_iff`.
