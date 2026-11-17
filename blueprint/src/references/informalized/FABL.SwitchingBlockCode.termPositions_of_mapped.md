<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/HastadSwitching.lean :: FABL.SwitchingBlockCode.termPositions_of_mapped -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Positions of a Mapped Term Code

**Claim.** For a DNF term $T$ of width at most $w$ and a set of positions in its literal list, mapping those positions into the first $w$ coordinates and constructing a code from the image gives exactly the original positions when viewed within $T$.

**Proof.** The constructed code has position set equal to the image of the given positions under the coordinate embedding. Its positions within $T$ are the preimage of that image under the same embedding. Because the embedding is injective, a literal position maps into this image exactly when it was in the original set. Thus the preimage is precisely the original set.
