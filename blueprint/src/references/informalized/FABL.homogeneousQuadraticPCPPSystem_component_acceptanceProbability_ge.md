<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/QuadraticPCPP.lean :: FABL.homogeneousQuadraticPCPPSystem_component_acceptanceProbability_ge -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Component Acceptance Lower Bounds

**Claim.** If the three-component verifier accepts with probability at least $1-\varepsilon/100000$, then each component accepts with probability at least $1-(3/100000)\varepsilon$.

**Proof.** Write the three testers as a family indexed by the three-element set. The overall acceptance hypothesis, together with the definition of the rejection rate, gives a lower bound of $1-((3/100000)/3)\varepsilon$ for the uniform mixture’s acceptance probability; the constants agree because the rejection rate is $1/100000$. For any component of a uniform mixture, acceptance at least $1-(\text{rate}/3)\varepsilon$ forces that component’s acceptance to be at least $1-\text{rate}\,\varepsilon$ (\texttt{component\_acceptanceProbability\_ge\_of\_uniformMixture\_ge}). Applying this fact to each of the three indices and substituting the rate $3/100000$ proves all three bounds.

**Key facts.** `FABL.component_acceptanceProbability_ge_of_uniformMixture_ge`.
