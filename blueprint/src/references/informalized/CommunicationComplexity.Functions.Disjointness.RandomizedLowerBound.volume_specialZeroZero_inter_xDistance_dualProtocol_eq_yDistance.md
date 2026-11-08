<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/ZFiberMeasure.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.volume_specialZeroZero_inter_xDistance_dualProtocol_eq_yDistance -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Duality of Special-Bit Bias Events

**Claim.** On the event that both special bits are zero, the volume of samples where Alice’s special-bit bias for the dual protocol exceeds $\gamma$ equals the volume of samples where Bob’s special-bit bias for the original protocol exceeds $\gamma$.

**Proof.** Let $S_{\mathrm{dual}}$ be the event that both special bits are zero and the dual protocol’s Alice bias exceeds $\gamma$, and let $S$ be the analogous event for the original protocol’s Bob bias. Under the dual-sample map, the zero-zero event is preserved (`specialZeroZero_dualHardSample`), and the $Z$-value transforms to its dual (`zVariable_dualProtocol_dualHardSample`). The bias at that dual value equals the original Bob bias (`xDistance_dualProtocol_dualZValue_eq_yDistance`). Thus the preimage of $S_{\mathrm{dual}}$ is exactly $S$. Since duality preserves the ambient volume (`volume_measurePreserving_dualHardSample`), the preimage and target have the same measure, so $S$ and $S_{\mathrm{dual}}$ have equal volume. Passing to real-valued measures yields the claim.

**Key facts.** `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.specialZeroZero_dualHardSample`, `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.zVariable_dualProtocol_dualHardSample`, `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.xDistance_dualProtocol_dualZValue_eq_yDistance`, `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.volume_measurePreserving_dualHardSample`.
