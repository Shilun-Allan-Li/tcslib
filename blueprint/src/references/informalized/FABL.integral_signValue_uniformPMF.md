<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/PrescribedFourierSupport.lean :: FABL.integral_signValue_uniformPMF -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Mean of a uniform sign

**Claim.** A sign chosen uniformly from $\{-1,1\}$ has expected value zero.

**Proof.** Convert the integral under the uniform sign law to expectation, then write that expectation as the average over the finite sign set (`integral_uniformPMF_eq_expect`). The two possible values are $-1$ and $1$, whose sum is zero; dividing by the number of signs therefore gives zero.

**Key facts.** `FABL.integral_uniformPMF_eq_expect`.
