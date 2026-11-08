<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/DualHardSample.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.xWindow_dualHardSample_eq_reverse -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Reversal of a Windowed Bit Vector

**Claim.** If the coordinate windows specified by $P$ and $Q$ correspond under reversal, then Alice’s bits retained by the window in the dual sample form the reversal of Bob’s bits retained by the corresponding window in the original sample.

**Proof.** Compare the two vectors at an arbitrary coordinate $i$. Alice’s bit in the dual sample at $i$ equals Bob’s bit in the original sample at $\operatorname{rev}(i)$ (`xBit_dualHardSample`). The two window conditions at these coordinates are equivalent by the assumed relation $h_{PQ}$. If the condition holds, both vectors retain those corresponding bits; if it fails, both entries are false. Thus the entries agree in either case, and the vectors are equal.

**Key facts.** `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.xBit_dualHardSample`.
