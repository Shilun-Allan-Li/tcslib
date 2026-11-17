<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/DualityMeasurePreserving.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.zVariable_dualProtocol_preimage_dualZValue -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Duality Pulls Back Z-Fibers

**Claim.** A sample's dual lies in the dual fiber over the dualized value exactly when the original sample lies in the original fiber.

**Proof.** Take an arbitrary sample and expand membership in the two fibers as equality of the corresponding $Z$-values. The duality identity for the $Z$-variable rewrites the left equality as $Z_p(\omega)^\dagger=z^\dagger$. Since dualization of achievable $Z$-values is injective (`dualZValue_injective`), this holds exactly when $Z_p(\omega)=z$. This is precisely membership in the original fiber.

**Key facts.** `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.zVariable_dualProtocol_dualHardSample`, `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.dualZValue_injective`.
