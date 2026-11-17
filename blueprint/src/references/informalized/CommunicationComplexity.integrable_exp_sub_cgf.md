<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/Pinsker.lean :: CommunicationComplexity.integrable_exp_sub_cgf -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Integrability of the centered exponential moment

**Claim.** If $x\mapsto e^{tX(x)}$ is integrable, then so is $x\mapsto e^{tX(x)-\Lambda(t)}$, where $\Lambda(t)$ is the cumulant generating function.

**Proof.** The exponential of the centered exponent factors as $e^{-\	ext{cgf}(X,\mu,t)}e^{tX(x)}$ (`exp_sub_cgf_eq`). The first factor is a finite constant independent of $x$, and multiplying an integrable function by a constant preserves integrability. Hence the centered exponential moment is integrable.

**Key facts.** `CommunicationComplexity.exp_sub_cgf_eq`.
