<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/AliceYFalse.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.yGeSpecial_eq_yAfterSpecial_of_specialY_false -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Suffix vectors when the special bit is false

**Claim.** If Bob’s bit at the special coordinate is false, then his vector from the special coordinate onward equals his vector strictly after the special coordinate, both padded with false elsewhere.

**Proof.** Compare the two vectors at a coordinate $j$. If $T<j$, then $T\le j$ as well, so both vectors retain Bob’s bit at $j$. If $T\not<j$ but $T\le j$, antisymmetry gives $j=T$; at this coordinate the vector starting at $T$ has value $y_T$, which is false by hypothesis, matching the strictly-after vector’s padded value. In the remaining case $T\not\le j$, neither vector includes the coordinate and both values are false. Thus the vectors agree everywhere.
