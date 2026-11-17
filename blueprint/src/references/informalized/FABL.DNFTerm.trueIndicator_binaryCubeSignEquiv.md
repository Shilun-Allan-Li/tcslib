<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/DNFSparsePolynomialThreshold.lean :: FABL.DNFTerm.trueIndicator_binaryCubeSignEquiv -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Indicator under binary sign encoding

**Claim.** For a DNF term $T$, its true indicator after coordinatewise binary-to-sign encoding is the indicator of the affine subspace through the satisfying binary base point, whose direction consists of vectors vanishing on the support of $T$.

**Proof.** Fix a binary vector $x$. First, membership in this affine subspace is equivalent to $x$ agreeing with the base point on every coordinate in the support. Indeed, affine-subspace membership says that $x$ plus the base point lies in the coordinate-zero subspace (mem_binaryAffineSubspace_iff_add_mem); the latter means that this sum vanishes on the support (mem_coordinateZeroSubspace_iff). Over the field with two elements, each element is its own negative, so vanishing of the sum is exactly coordinatewise agreement.

Next, this agreement is equivalent to the encoded sign vector satisfying every literal of $T$. On a supported coordinate, the base point was defined as the binary preimage of the literal's required sign, so encoding it gives precisely that required sign. Conversely, if the encoded vector has the required sign, injectivity of the binary-to-sign bijection forces the binary coordinate to equal the base point there. The term evaluates to $-1$ exactly when all supported coordinates have their required signs (eval_eq_neg_one_iff_requiredAt), and the encoding acts coordinatewise (binaryCubeSignEquiv_apply). Thus affine-subspace membership is equivalent to the term evaluating to $-1$.

Finally, split according to whether the term evaluates to $-1$. In that case both indicators are $1$; otherwise the point is outside the affine subspace and both indicators are $0$.

**Key facts.** `FABL.mem_binaryAffineSubspace_iff_add_mem`, `FABL.F₂DecisionTree.mem_coordinateZeroSubspace_iff`, `FABL.DNFTerm.eval_eq_neg_one_iff_requiredAt`, `FABL.binaryCubeSignEquiv_apply`.
