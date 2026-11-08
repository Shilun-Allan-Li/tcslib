<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/DualHardSample.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.Y_dualHardSample -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Duality of Bob's input set

**Claim.** Bob's input set in the dual sample is the coordinate reversal of Alice's input set in the original sample.

**Proof.** Apply the identity for Alice's set in a dual sample (`X_dualHardSample`) to the dual of the given sample. It states that Alice's set after dualizing twice is the reversal of Bob's set in the once-dualized sample. Since dualizing twice returns the original sample (`dualHardSample_dualHardSample`), this gives $X(\omega)=\operatorname{reverse}(Y(\operatorname{dual}(\omega)))$. Reverse both sides; reversing twice returns the original set (`reverseSet_reverseSet`), yielding the desired equality.

**Key facts.** `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.X_dualHardSample`, `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.dualHardSample_dualHardSample`, `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.reverseSet_reverseSet`.
