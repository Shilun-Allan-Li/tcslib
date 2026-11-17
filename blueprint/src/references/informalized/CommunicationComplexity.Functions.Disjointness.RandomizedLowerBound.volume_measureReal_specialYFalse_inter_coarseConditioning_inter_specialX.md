<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/FuncDisjointnessLowerBound/AliceYFalse.lean :: CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.volume_measureReal_specialYFalse_inter_coarseConditioning_inter_specialX -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Equal mass for special-bit halves

**Claim.** Within the event where Bob's special bit is false and the coarse conditioning equals a fixed value, either specified value of Alice's special bit has exactly half the total mass.

**Proof.** Fix the fiber defined by Bob's special bit being false and the coarse conditioning value. Flipping Alice's special bit leaves Bob's bit and the coarse conditioning unchanged, and toggles Alice's special bit (`specialY_flipSpecialX`, `coarseConditioning_flipSpecialX`, `specialX_flipSpecialX`). Since this flip preserves volume (`volume_measurePreserving_flipSpecialX`), the false-bit and true-bit portions of the fiber have equal mass. These two portions are disjoint and partition the fiber, because Alice's special bit is either false or true. Therefore each portion has half the fiber's mass, which proves the assertion for either choice of $b$.

**Key facts.** `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.specialY_flipSpecialX`, `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.coarseConditioning_flipSpecialX`, `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.specialX_flipSpecialX`, `CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound.volume_measurePreserving_flipSpecialX`.
