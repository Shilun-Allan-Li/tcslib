<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/Headline.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.zFiber_inter_diag_specialPair_subset_protocolErrorEvent -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Diagonal Pairs Force an Error

**Claim.** Every sample in the fiber of an achievable value whose special pair equals the transcript output on both coordinates is an error of the protocol.

**Proof.** Fix such a sample and write $b$ for the output recorded by the fiber's transcript. The protocol's actual output on this sample is $b$, by the fact that the protocol output is determined by its transcript on the fiber (`run_eq_zOutput_of_zVariable_eq`). The special pair is $(b,b)$. Split on the two possible values of $b$. If $b=\mathrm{false}$, both special bits are false. The inputs are then disjoint: any common coordinate would contradict `disjoint_X_Y_iff`, since that fact characterizes disjointness by the absence of a coordinate where both special bits are true. Thus the correct disjointness output is true, contrary to the protocol's output. If $b=\mathrm{true}$, both special bits are true, so the inputs are not disjoint by the same characterization. The correct output is false, again contrary to the protocol's output. In either case the sample belongs to the protocol's error event.

**Key facts.** `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.run_eq_zOutput_of_zVariable_eq`, `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.disjoint_X_Y_iff`.
