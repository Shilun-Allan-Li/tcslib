<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/HastadThreeSat.lean :: FABL.oxrAcceptanceProbability_dictator -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Dictator acceptance probability

**Claim.** For any $n$, any $\delta\in[0,1]$, and any coordinate $i$, the specified OXR test accepts the dictator $x\mapsto x_i$ with probability $1$.

**Proof.** The dictator is odd, and its real-valued form is the singleton monomial $\chi_{\{i\}}$ (dictator_toReal_eq_monomial_singleton). The OXR acceptance identity for odd functions (oxrAcceptanceProbability_eq_equationSevenSeven) expresses its acceptance probability using its noise stability and a Fourier-weighted random-subset average. The dictator's noise stability at correlation $-\delta$ is $-\delta$ (noiseStability_dictator). Its Fourier coefficients vanish except at $\{i\}$, where the coefficient is $1$ (fourierCoeff_monomial). For that singleton, the random-subset average is $-(1-\delta)$: the intersection expansion (expectDeltaRandomSubset_intersection_eq_sum) leaves only the subset $\{i\}$, with its corresponding factor $-(1-\delta)$. Thus the weighted Fourier sum is also $-(1-\delta)$. Substituting both values into the acceptance identity gives $3/4-(-\delta)/4-(-(1-\delta))/4=1$.

**Key facts.** `FABL.dictator_toReal_eq_monomial_singleton`, `FABL.expectDeltaRandomSubset_intersection_eq_sum`, `FABL.fourierCoeff_monomial`, `FABL.noiseStability_dictator`, `FABL.oxrAcceptanceProbability_eq_equationSevenSeven`.
