<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/F₂Polynomials/CompleteQuadraticDecomposition.lean :: FABL.pairedCoordinateEquiv_succ_right_castSucc -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Preservation of Existing Right Coordinates

**Claim.** For each existing right paired-coordinate index $r+2j+1$, the image of the appended vector under the automorphism for $k+1$ pairs agrees there with the image of $x$ under the automorphism for $k$ pairs.

**Proof.** The appended-pair formula (\texttt{FABL.pairedCoordinateEquiv_succ_appendTwo}) says that the transformed vector consists of the image of $x$ followed by the two new tail coordinates. The index for the existing right coordinate lies in that prefix, so its value is exactly the value of the image of $x$ at index $r+2j+1$.

**Key facts.** `FABL.pairedCoordinateEquiv_succ_appendTwo`.
