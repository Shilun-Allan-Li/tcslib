<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Tribes.lean :: FABL.finProdFinEquiv_tribesCoord -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Tribes Coordinate Inverse Identity

**Claim.** For natural numbers $w,s$ and any index $i$ among the $sw$ coordinates, applying the canonical pairing map from a pair of indices in blocks of sizes $s$ and $w$ to the pair of coordinates associated to $i$ returns $i$.

**Proof.** The associated pair of coordinates is defined by applying the inverse of the canonical pairing equivalence to $i$. Applying the equivalence to that inverse image returns the original index, by the inverse law for equivalences.
