<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/AlgebraicPCPP.lean :: FABL.completeQuadraticLinearPCPPSystem_rejectionProbability -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Rejection as Uniform Failure

**Claim.** The verifier’s rejection probability on input $w$ and proof $\pi$ is the uniform probability that its corresponding check fails.

**Proof.** Using the definitions of rejection and acceptance probability, the rejection probability is one minus the expected acceptance indicator. The seed distribution is uniform, so the expectation of that indicator is the uniform expectation over the finite seed space (`pmfExpectation_uniformPMF_eq_expect`). Since the expectation of the constant one is one, linearity of expectation rewrites the rejection probability as the expectation of one minus the acceptance indicator. For each seed, the verifier’s queries return exactly the input and proof entries specified by that seed; its transcript predicate accepts precisely when the corresponding check holds. Thus one minus the acceptance indicator is the indicator that the check fails. This identification is verified by splitting into endpoint seeds and transition seeds, then into each Boolean check type; in every case, the verifier accepts exactly when the defining equality or Boolean condition holds. The resulting expectation is the uniform probability of failure.

**Key facts.** `FABL.pmfExpectation_uniformPMF_eq_expect`.
