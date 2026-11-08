<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/F₂Polynomials/CompleteQuadraticDecomposition.lean :: FABL.pairedCoordinateEquiv_succ_left_last -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Value at the New Left Coordinate

**Claim.** The coordinate at index $r+2k$ of the transformed appended vector is $a+\sum_i x_i$.

**Proof.** By the appended-pair formula (\texttt{FABL.pairedCoordinateEquiv_succ_appendTwo}), the transformed vector is the image of $x$ followed by the two coordinates $a+\sum_i x_i$ and $b+\sum_i x_i$. The index $r+2k$ selects the first of these two appended coordinates, giving the claimed value.

**Key facts.** `FABL.pairedCoordinateEquiv_succ_appendTwo`.
