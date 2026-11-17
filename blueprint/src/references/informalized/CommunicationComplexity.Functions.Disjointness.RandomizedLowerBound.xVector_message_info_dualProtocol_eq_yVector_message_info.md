<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/InformationTerms.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.xVector_message_info_dualProtocol_eq_yVector_message_info -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Duality of Conditional Transcript Information

**Claim.** Under the hard distribution conditioned on disjoint inputs, the conditional mutual information between Alice’s vector and the dual protocol’s transcript given Bob’s vector equals the conditional mutual information between Bob’s vector and the original protocol’s transcript given Alice’s vector.

**Proof.** 1. Write $\mu$ for the hard distribution conditioned on disjoint inputs. The dual-sample map preserves this measure (`disjointCondMeasure_measurePreserving_dualHardSample`). Therefore the original triple consisting of Alice’s vector, the dual protocol’s transcript, and Bob’s vector has the same distribution as the triple obtained by evaluating all three after applying the dual-sample map (`identDistrib_self_comp_measurePreserving`). Invariance of conditional mutual information under equality in distribution (`ProbabilityTheory.IdentDistrib.condMutualInfo_eq_finite`) lets us replace the first expression by this pulled-back one.

2. The pulled-back variables can be identified explicitly. The duality identities for the input vectors (`xVector_dualHardSample`, `yVector_dualHardSample`) express them as reversals of Bob’s and Alice’s original vectors. The transcript transport identity (`message_dualProtocol_dualHardSample`) expresses the pulled-back transcript as the image of the original transcript under the dual transcript map.

3. Reversal is injective (`reverseBoolVector_injective`), and the transcript transport map is injective (`dualProtocolTranscriptMap_injective`). Conditional mutual information is unchanged when each of its three variables is recoded injectively (`ProbabilityTheory.condMutualInfo_of_inj'`). Applying this to the original triple—Bob’s vector, the original transcript, and Alice’s vector—identifies its information with that of the pulled-back triple. Combining this with the first step gives the desired equality.

**Key facts.** `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.disjointCondMeasure_measurePreserving_dualHardSample`, `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.identDistrib_self_comp_measurePreserving`, `ProbabilityTheory.IdentDistrib.condMutualInfo_eq_finite`, `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.reverseBoolVector_injective`, `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.dualProtocolTranscriptMap_injective`, `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.xVector_dualHardSample`, `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.yVector_dualHardSample`, `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.message_dualProtocol_dualHardSample`.
