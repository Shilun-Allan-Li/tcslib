<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/Pinsker.lean :: CommunicationComplexity.integral_klFun_rnDeriv_eq_kl_integral -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Two integral forms of relative entropy

**Claim.** Under the stated absolute continuity and integrability assumptions, the integral of $\varphi(d\mu/d\nu)$ against $\nu$ equals the integral of the log-likelihood ratio against $\mu$.

**Proof.** Apply the established Radon–Nikodym integral identity for the Kullback–Leibler integrand: under $\mu\ll\nu$ and integrability of the log-likelihood ratio, the integral of $\mathrm{klFun}(d\mu/d\nu)$ against $\nu$ equals its integral against $\mu$ (`InformationTheory.integral_klFun_rnDeriv`). Rewriting the real-valued density and the log-likelihood ratio in the notation of the claim gives the asserted equality, since the integrand on the $\mu$ side is the log-likelihood ratio.
