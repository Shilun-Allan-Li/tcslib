<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/Pinsker.lean :: CommunicationComplexity.integral_exp_sub_cgf_eq_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Normalization of the exponential tilt

**Claim.** If $x\mapsto e^{tX(x)}$ is integrable under the probability measure $\mu$, then the exponential tilt normalized by the cumulant generating function has integral one.

**Proof.** The exponential in the integrand factors as $e^{-\Lambda(t)}e^{tX(x)}$ (`CommunicationComplexity.exp_sub_cgf_eq`). Since the first factor is constant in $x$, its integral is $e^{-\Lambda(t)}$ times the moment generating function $M_X(t)$. By the relation $e^{\Lambda(t)}=M_X(t)$ under the stated integrability assumption, this product is $e^{-\Lambda(t)}e^{\Lambda(t)}=1$.

**Key facts.** `CommunicationComplexity.exp_sub_cgf_eq`.
