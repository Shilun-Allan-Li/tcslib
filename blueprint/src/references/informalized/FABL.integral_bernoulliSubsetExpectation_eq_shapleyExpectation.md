<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/BiasedThresholdPhenomena.lean :: FABL.integral_bernoulliSubsetExpectation_eq_shapleyExpectation -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bernoulli and Shapley Expectations

**Claim.** Integrating the Bernoulli subset expectation over $p\in[0,1]$ gives the Shapley subset expectation.

**Proof.** Expand the Bernoulli expectation as a finite sum over subsets $S$. Since each summand is continuous in $p$, integrate the sum term by term. For a fixed $S$, factor out the constant $f(S)$; the remaining integral is the Bernoulli mass of a subset of size $|S|$. The identity that this mass equals the Shapley layer weight (\(\texttt{integral\_bernoulliSubsetMass\_eq\_shapleyLayerWeight}\)) turns the term into the layer weight times $f(S)$. The Shapley subset distribution assigns to each $S$ a probability whose real value is exactly that layer weight (\(\texttt{shapleySubsetPMF\_apply\_toReal\_eq\_layerWeight}\)). Thus the resulting sum is the expectation under the Shapley subset distribution, as claimed.

**Key facts.** `FABL.integral_bernoulliSubsetMass_eq_shapleyLayerWeight`, `FABL.shapleySubsetPMF_apply_toReal_eq_layerWeight`.
