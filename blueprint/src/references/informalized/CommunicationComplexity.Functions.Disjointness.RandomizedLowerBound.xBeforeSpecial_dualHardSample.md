<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/DualHardSample.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.xBeforeSpecial_dualHardSample -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Duality of Windowed Bit Vectors

**Claim.** The before-special Alice vector of the dual sample is the coordinate reversal of the after-special Bob vector of the original sample.

**Proof.** Apply the shared window-reversal identity (`xWindow_dualHardSample_eq_reverse`) with the predicate selecting coordinates strictly before the dual special coordinate and the predicate selecting coordinates strictly after the original special coordinate. These two cuts match under coordinate reversal: $i<\operatorname{rev}(T)$ exactly when $T<\operatorname{rev}(i)$, by the order-reversal property of `Fin.rev` (`Fin.lt_rev_iff`). The identity then gives the required equality of vectors.

**Key facts.** `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.xWindow_dualHardSample_eq_reverse`.
