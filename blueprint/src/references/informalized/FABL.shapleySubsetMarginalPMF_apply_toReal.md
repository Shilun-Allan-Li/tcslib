<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/BiasedThresholdComplements.lean :: FABL.shapleySubsetMarginalPMF_apply_toReal -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Marginal Subset Probability

**Claim.** For a subset $J$ of an $n$-element set and a subset $T\subseteq J$, the probability that a Shapley-random subset restricts to $T$ is $1/((|J|+1)\binom{|J|}{|T|})$.

**Proof.** The probability of the restriction being $T$ is the sum of the probabilities of all subsets $S$ whose restriction to $J$ is $T$. Each such $S$ is uniquely obtained by adjoining to the lift of $T$ an arbitrary subset $U$ of the complement of $J$. The restriction and reconstruction identities (`FABL.restrictSubsetTo_union_compl` and `FABL.lift_restrict_union_sdiff`) establish this correspondence; uniqueness follows by recovering $U$ as $S\setminus J$ (`FABL.sdiff_lift_union_compl`). The reconstructed subset has cardinality $|T|+|U|$, since the lift has cardinality $|T|$ (`FABL.card_liftSubsetFrom`) and is disjoint from $U$ (`FABL.disjoint_liftSubsetFrom_of_subset_compl`). Its Shapley probability is therefore the layer weight for that cardinality (`FABL.shapleySubsetPMF_apply_toReal_eq_layerWeight`). Summing over all $U\subseteq J^c$ gives the complement-sum identity (`FABL.sum_shapleyLayerWeight_add_card_compl`), which equals the layer weight on a ground set of size $|J|$ at cardinality $|T|$. This is the asserted probability.

**Key facts.** `FABL.restrictSubsetTo_union_compl`, `FABL.lift_restrict_union_sdiff`, `FABL.sdiff_lift_union_compl`, `FABL.card_liftSubsetFrom`, `FABL.disjoint_liftSubsetFrom_of_subset_compl`, `FABL.shapleySubsetPMF_apply_toReal_eq_layerWeight`, `FABL.sum_shapleyLayerWeight_add_card_compl`.
