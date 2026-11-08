<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/MajorityNoiseStability.lean :: FABL.exists_majorityNoiseStability_constant -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Bounds for odd-majority noise stability

**Claim.** There is a positive constant $C$ such that, for every $0<\rho<1$, the noise stability of majority on odd-dimensional cubes is antitone in the dimension parameter and lies between $(2/\pi)\arcsin\rho$ and that value plus $C/[\sqrt{1-\rho^2}\sqrt{2m+1}]$.

**Proof.** Choose a positive constant $C$ for which the odd-majority upper estimate holds, as supplied by `exists_noiseStability_majority_odd_le_arcsine_add_inv_sqrt`. For each $0<\rho<1$, the odd-dimensional stability sequence is antitone by `noiseStability_majority_odd_antitone`. At each index $m$, its lower bound is $(2/\pi)\arcsin\rho$ by `two_div_pi_mul_arcsin_le_noiseStability_majority_odd`, while the chosen upper estimate gives the claimed error term. Combining these statements proves all the required bounds.

**Key facts.** `FABL.exists_noiseStability_majority_odd_le_arcsine_add_inv_sqrt`, `FABL.noiseStability_majority_odd_antitone`, `FABL.two_div_pi_mul_arcsin_le_noiseStability_majority_odd`.
