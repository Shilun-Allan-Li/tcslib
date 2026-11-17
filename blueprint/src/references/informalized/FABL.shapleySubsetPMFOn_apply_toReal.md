<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/BiasedThresholdComplements.lean :: FABL.shapleySubsetPMFOn_apply_toReal -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Probability of a Subset of a Finite Set

**Claim.** For a subset $T$ of $J$, its probability under the Shapley subset distribution on $J$ is $1/((|J|+1)\binom{|J|}{|T|})$.

**Proof.** The distribution on subsets of $J$ is obtained by transporting the Shapley subset distribution on $|J|$ elements along the inverse of the enumeration equivalence. The mass of a mapped point is the mass of its inverse image (`pmf_map_equiv_apply`). That inverse image has the same cardinality as $T$, since the equivalence preserves membership and cardinality. The probability formula for a subset of a fixed size, expressed as its Shapley layer weight (`shapleySubsetPMF_apply_toReal_eq_layerWeight`), therefore gives the stated value.

**Key facts.** `FABL.pmf_map_equiv_apply`, `FABL.shapleySubsetPMF_apply_toReal_eq_layerWeight`.
