<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/CoordinateVectorModel.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.coordinateAliceConditioningOfCondBits_injective -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Injectivity of the split encoding

**Claim.** The map that splits a bit-string at coordinate $i$, placing its bits below $i$ in the first component and its bits at or above $i$ in the second, is injective.

**Proof.** Suppose two bit-strings have the same encoded pair. Fix any coordinate $j$. If $j<i$, the first component at $j$ equals the original bit at $j$, so equality of the first components gives equality of the two strings there. If $j\not<i$, then $i\le j$; the second component at $j$ equals the original bit, and equality of the second components gives equality there. Thus the strings agree at every coordinate and are equal.
