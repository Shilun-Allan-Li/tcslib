<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/ZFiberMeasure.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.dualHardSample_preimage_zVariable_dualZValue_inter_specialX -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Duality of Z-fibers and special bits

**Claim.** Taking the preimage under sample duality of the dual $Z$-fiber with Alice’s special bit equal to $b$ gives the original $Z$-fiber with Bob’s special bit equal to $b$.

**Proof.** For a sample $\omega$, membership on the left says that its dual has $Z$-value equal to the dual of $z$ and has Alice’s special bit equal to $b$. The sample-to-$Z$ compatibility under duality (`zVariable_dualProtocol_dualHardSample`) identifies the first condition with $D_Z(Z_p(\omega))=D_Z(z)$, where $D_Z$ is the dual $Z$-value map. Since that map is injective (`dualZValue_injective`), this is equivalent to $Z_p(\omega)=z$. The special-bit compatibility (`specialX_dualHardSample`) identifies the second condition with Bob’s special bit of $\omega$ being $b$. Thus membership on the left is equivalent to membership on the right for every sample, proving equality of the sets.

**Key facts.** `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.zVariable_dualProtocol_dualHardSample`, `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.specialX_dualHardSample`, `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.dualZValue_injective`.
