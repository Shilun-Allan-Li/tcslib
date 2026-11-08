<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Parity.lean :: FABL.parityFunction_univ_flipCoordinate -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Flipping Reverses Full Parity

**Claim.** For every Boolean-cube input and coordinate, flipping that coordinate negates the parity over all coordinates.

**Proof.** Write full parity as the product of all coordinate signs. Updating coordinate $i$ in this product replaces its factor by $-x_i$ while leaving every other factor unchanged. Since $i$ belongs to the full coordinate set, the product is therefore the negative of its original value.
