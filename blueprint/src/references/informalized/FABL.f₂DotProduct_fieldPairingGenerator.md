<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/SmallBiasVariants.lean :: FABL.f₂DotProduct_fieldPairingGenerator -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Pairing Through a Binary Extension Field

**Claim.** The dot product of γ with the vector of pairings between the encoded elements aᵢ and s equals the dot product of the encoding of their γ-weighted sum with the encoding of s.

**Proof.** Because the encoding is linear, it sends the weighted sum defining the field coefficient to the coordinatewise weighted sum of the encodings: it preserves finite sums and scalar multiplication. Substitute this identity and expand the dot products. Distribute each γₓ across the sum over basis coordinates, rearrange the finite sums so that the basis coordinate is summed first, and factor out the corresponding coordinate of the encoding of s. This gives the dot product of the encoded weighted sum with the encoding of s.
