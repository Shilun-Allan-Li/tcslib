<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/BiasedThresholdPhenomena.lean :: FABL.shapleySubsetPMF_apply_toReal_eq_layerWeight -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Subset Probability Equals Layer Weight

**Claim.** The real probability of selecting $S$ under the Shapley subset distribution equals its Shapley layer weight, $1/((n+1)\binom{n}{|S|})$.

**Proof.** The real-probability formula gives $(n+1)^{-1}\binom{n}{|S|}^{-1}$ (`shapleySubsetPMF_apply_toReal`). By definition, this is exactly the Shapley layer weight at size $|S|$.

**Key facts.** `FABL.shapleySubsetPMF_apply_toReal`.
