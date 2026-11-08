<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/F₂Polynomials/CompleteQuadraticDecomposition.lean :: FABL.pairedCoordinateEquiv_succ_right_last -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Value at the New Right Coordinate

**Claim.** The coordinate at index $r+2k+1$ of the transformed appended vector is $b+\sum_i x_i$.

**Proof.** The appended-pair formula (\texttt{FABL.pairedCoordinateEquiv_succ_appendTwo}) identifies the transformed vector as the image of $x$ followed by $a+\sum_i x_i$ and $b+\sum_i x_i$. The index $r+2k+1$ selects the second of these appended coordinates, so its value is $b+\sum_i x_i$.

**Key facts.** `FABL.pairedCoordinateEquiv_succ_appendTwo`.
