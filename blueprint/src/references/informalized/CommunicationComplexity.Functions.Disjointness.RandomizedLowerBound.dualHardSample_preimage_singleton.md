<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/DualityMeasurePreserving.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.dualHardSample_preimage_singleton -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Singleton preimage under dualization

**Claim.** For each hard sample $\omega$, the preimage of $\{\omega\}$ under dualization is exactly $\{D(\omega)\}$.

**Proof.** Check membership in the two sets. If a sample $\omega'$ lies in the preimage, then $D(\omega')=\omega$. Applying $D$ to this equality and using that dualization applied twice is the identity gives $\omega'=D(\omega)$. Conversely, if $\omega'=D(\omega)$, then $D(\omega')=D(D(\omega))=\omega$, so $\omega'$ lies in the preimage. These two implications establish the claimed equality of singletons.

**Key facts.** `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.dualHardSample_dualHardSample`.
