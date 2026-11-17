<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/HardDistributionEvents.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.disjointSpecialYFalseMeasure_measureReal_specialX_singleton -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Uniformity of the Special Bit

**Claim.** Under the hard distribution conditioned on disjointness and on Bob’s special bit being false, Alice’s special bit takes either Boolean value with probability exactly $1/2$.

**Proof.** Conditioning once more on Bob’s special bit being false divides the disjointness-conditioned mass of its intersection with the event $X_T=b$ by the mass of the false-bit event, which is $2/3$ (\texttt{disjointCondMeasure_measureReal_specialY_false}). Split into the two possible values of $b$. For $b=\mathrm{false}$, the numerator is the mass of the special-bit pair $(X_T,Y_T)=(\mathrm{false},\mathrm{false})$, namely $1/3$ (\texttt{disjointCondMeasure_measureReal_specialZeroZero}). For $b=\mathrm{true}$, the numerator is the mass of the pair $(\mathrm{true},\mathrm{false})$, also $1/3$ (\texttt{disjointCondMeasure_measureReal_specialBitsEvent}); this pair is compatible with disjointness. In either case the conditional probability is $(1/3)/(2/3)=1/2$.

**Key facts.** `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.disjointCondMeasure_measureReal_specialY_false`, `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.disjointCondMeasure_measureReal_specialZeroZero`, `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.disjointCondMeasure_measureReal_specialBitsEvent`.
