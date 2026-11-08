<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/HardDistributionEvents.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.hardSample_measureReal_fieldProduct -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Product Formula for Rectangle Events

**Claim.** The measure of a rectangle event specified independently by restrictions on the special coordinate, the two special bits, and the remaining coordinate vector equals the product of the corresponding uniform marginal masses.

**Proof.** Let $E$ be the specified rectangle event. Since the hard-sample space has the uniform law, its mass is the number of points in $E$ divided by the total number of hard samples (\texttt{uniformOn\_univ\_measureReal\_eq\_card\_subtype}). The event's subtype is in bijection with the product of the four subtypes defined by the respective restrictions: a sample gives its four components, and four admissible components reconstruct the sample. Thus the event's cardinality is the product of the four restricted cardinalities. Each factor's uniform mass is its restricted cardinality divided by the size of its ambient space: for the special coordinate use \texttt{uniformFin\_real}, for each bit use \texttt{uniformBool\_real}, and for the coordinate vector use \texttt{uniformDisjointCoordinateVector\_real}. The total number of hard samples is $n\cdot4\cdot3^n$ (\texttt{HardSample.card}), matching the product of the four ambient cardinalities. Clearing these nonzero denominators gives the asserted product identity.

**Key facts.** `CommunicationComplexity.uniformOn_univ_measureReal_eq_card_subtype`, `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.uniformFin_real`, `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.uniformBool_real`, `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.uniformDisjointCoordinateVector_real`, `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.HardSample.card`.
