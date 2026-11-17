<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/F₂Polynomials/CompleteQuadraticDecomposition.lean :: FABL.pairedCoordinateEquiv_succ_left_castSucc -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Preservation of Existing Left Coordinates

**Claim.** For each existing left paired-coordinate index $r+2j$, the image of the appended vector under the automorphism for $k+1$ pairs agrees there with the image of $x$ under the automorphism for $k$ pairs.

**Proof.** The appended-pair formula (\texttt{FABL.pairedCoordinateEquiv_succ_appendTwo}) expresses the transformed vector as the image of $x$ followed by the two new tail coordinates. The index corresponding to $j$ among the first $k$ pairs is still within that prefix. Reading that coordinate therefore gives the value of the image of $x$ at its left index $r+2j$.

**Key facts.** `FABL.pairedCoordinateEquiv_succ_appendTwo`.
