<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/DualHardSample.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.xLeSpecial_dualHardSample -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Reversal of Truncated Inputs

**Claim.** For a hard sample, Alice’s vector in the dual sample, retaining coordinates at or before its special coordinate, is the reversal of Bob’s vector in the original sample, retaining coordinates at or after its special coordinate.

**Proof.** Use the general window-reversal identity (`xWindow_dualHardSample_eq_reverse`) with the two windows given by being at or before the respective special coordinates. The hypothesis relating the windows is exactly the order-reversal equivalence: $i\leq \operatorname{rev}(T)$ if and only if $T\leq\operatorname{rev}(i)$. The identity then says that the retained Alice bits in the dual sample equal the reversed retained Bob bits in the original sample, coordinate by coordinate.

**Key facts.** `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.xWindow_dualHardSample_eq_reverse`.
