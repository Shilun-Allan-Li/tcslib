<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/QuadraticCircuitReduction.lean :: FABL.BooleanCircuit.circuitQuadraticFourQueryPCPPSystem_component_acceptanceProbability_ge -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Acceptance of Each Component

**Claim.** If the combined verifier accepts with probability at least $1-\rho_C\varepsilon$, then each of its inner-function and input-consistency testers accepts the combined input-proof word with probability at least $1-\rho_Q\varepsilon$.

**Proof.** View the combined verifier as the uniform mixture of the two component testers. The given lower bound, together with the relation between the circuit and homogeneous quadratic rejection rates, gives the mixture acceptance bound in the form required by the component acceptance lemma. That lemma says that if a uniform mixture over $t$ testers accepts with probability at least $1-(\text{rate}/t)\varepsilon$, then every component accepts with probability at least $1-\text{rate}\cdot\varepsilon$ (`component_acceptanceProbability_ge_of_uniformMixture_ge`). Applying it to each of the two components yields the two asserted bounds.

**Key facts.** `FABL.component_acceptanceProbability_ge_of_uniformMixture_ge`.
