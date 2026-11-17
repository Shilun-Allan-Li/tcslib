<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/FriedgutNecessity.lean :: FABL.addressingSelectedCoordinate_flip -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Selected Coordinate Is Flip-Invariant

**Claim.** For every natural number $m$ and sign vector $x$ of length $m+2^m$, the coordinate selected using the address coordinates is unchanged after that selected coordinate is flipped.

**Proof.** The selected coordinate is obtained by applying the address equivalence and then the data-coordinate map to the first component of the decomposed input. By address preservation under a selected flip (FABL.addressingInputEquiv_first_flip_selected), that first component is unchanged by the flip. Applying the same address equivalence and data-coordinate map to equal first components gives equal selected coordinates.

**Key facts.** `FABL.addressingInputEquiv_first_flip_selected`.
