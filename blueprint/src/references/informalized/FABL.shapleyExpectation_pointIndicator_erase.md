<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/BiasedThresholdPhenomena.lean :: FABL.shapleyExpectation_pointIndicator_erase -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Erased-Set Indicator Expectation

**Claim.** The Shapley expectation of the indicator that erasing $i$ from the sampled subset gives $A$ is the sum of the probabilities of $A$ and $A\cup\{i\}$ if $i\notin A$, and is zero if $i\in A$.

**Proof.** Expand the expectation as a sum over sampled subsets. If $i\in A$, no subset can have its erasure equal to $A$, since an erased set never contains $i$; every indicator term is therefore zero. If $i\notin A$, the characterization of erasure (`FABL.erase_eq_fixed_iff`) says that a subset erases to $A$ exactly when it is either $A$ or $A\cup\{i\}$. Thus all other terms vanish, and the sum reduces to the probabilities of these two subsets; their indicators both equal one. This gives the stated formula.

**Key facts.** `FABL.erase_eq_fixed_iff`.
