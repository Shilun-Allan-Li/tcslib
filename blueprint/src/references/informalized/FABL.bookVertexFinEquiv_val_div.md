<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/MatchingMomentCombinatorics.lean :: FABL.bookVertexFinEquiv_val_div -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Index of a book vertex

**Claim.** For $k>0$, dividing the enumerated index of a vertex in a book with $q$ parts and $k$ vertices per part by $k$ gives the index of its part.

**Proof.** Write the vertex as a pair consisting of a part and a position within that part. The specified enumeration assigns it index $\text{position}+k\cdot\text{part}$. Dividing by $k$, the position contributes quotient zero because it is less than $k$, while the second summand contributes exactly the part index. The assumption $k>0$ ensures this quotient calculation is valid.
