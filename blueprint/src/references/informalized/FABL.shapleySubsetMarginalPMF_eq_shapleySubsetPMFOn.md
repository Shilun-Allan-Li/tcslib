<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/BiasedThresholdComplements.lean :: FABL.shapleySubsetMarginalPMF_eq_shapleySubsetPMFOn -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Marginal Distribution on a Subset

**Claim.** Restricting a Shapley-random subset to $J$ gives the same distribution as the Shapley subset distribution on a ground set of size $|J|$, with the elements identified through the enumeration of $J$.

**Proof.** To show the two probability distributions are equal, compare their probabilities at an arbitrary subset $T$ of $J$. The marginal distribution assigns probability whose real value is the layer weight at cardinality $|T|$ (`FABL.shapleySubsetMarginalPMF_apply_toReal`). The Shapley distribution on the enumerated ground set has the same real-valued probability (`FABL.shapleySubsetPMFOn_apply_toReal`). Since both probabilities are finite, equality of their real values implies equality of the probabilities themselves. Equality at every subset gives equality of the distributions.

**Key facts.** `FABL.shapleySubsetMarginalPMF_apply_toReal`, `FABL.shapleySubsetPMFOn_apply_toReal`.
