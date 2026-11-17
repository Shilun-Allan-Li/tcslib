<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/Pinsker.lean :: CommunicationComplexity.two_mul_tvDistance_sq_le_toReal_klDiv -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Pinsker Bound in Real Form

**Claim.** For probability measures with finite relative entropy, twice the square of their total variation distance is at most the real-valued relative entropy.

**Proof.** Pinsker's inequality gives the extended-real inequality that the real number $2\,\mathrm{TV}(\mu,\nu)^2$, viewed in the extended reals, is at most the relative entropy ($\texttt{pinsker\_inequality}$). The finite-entropy hypothesis allows the order-preserving conversion of this inequality to real values. Since the squared distance is nonnegative, its extended-real embedding converts back to the original real number, yielding the claimed bound.

**Key facts.** `CommunicationComplexity.pinsker_inequality`.
