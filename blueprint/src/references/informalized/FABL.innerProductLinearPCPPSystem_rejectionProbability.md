<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/AlgebraicPCPP.lean :: FABL.innerProductLinearPCPPSystem_rejectionProbability -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Uniform rejection probability

**Claim.** For every positive natural number $m$, input word $w$, and proof, the verifier's rejection probability equals the fraction of its seeds for which the corresponding check fails.

**Proof.** The verifier rejects exactly when its deterministic acceptance predicate says that the queried transcript fails the check specified by its seed. Its seed distribution is uniform. Rewriting rejection probability as one minus acceptance probability, then expressing acceptance as an expectation over seeds, identifies rejection with the uniform average of the indicator of check failure. For each seed, the transcript contains precisely the queried input and proof bits; in the endpoint cases this tests the specified prefix bit, and in the coordinate cases it tests either the product equation or the prefix-sum recurrence. Thus the acceptance indicator is the complement of the check-failure indicator seed by seed. Finally, uniform expectation of that indicator is the fraction of seeds for which the check fails (`pmfExpectation_uniformPMF_eq_expect`).

**Key facts.** `FABL.pmfExpectation_uniformPMF_eq_expect`.
