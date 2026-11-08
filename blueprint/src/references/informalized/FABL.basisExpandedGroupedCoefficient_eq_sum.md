<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/SmallBiasVariants.lean :: FABL.basisExpandedGroupedCoefficient_eq_sum -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Grouped coefficient expansion

**Claim.** The extension-field element encoded by the coefficients in the $i$th block is the sum, over $j\in\mathrm{Fin}(\ell)$, of $\gamma(i,j)$ times the $j$th basis vector.

**Proof.** Apply the encoding map to both sides; since it is injective, it suffices to show their images agree. The image of the grouped coefficient is, by the definition of encoding, the function whose $j$th coordinate is $\gamma(i,j)$. The encoding is linear, and it sends the $j$th basis vector to the function supported at $j$ with value $1$ (\(\texttt{binaryExtensionEncode\_basisVector}\)). Hence the image of the proposed sum has at coordinate $k$ the sum of the terms supported there: only the term with $j=k$ contributes, giving $\gamma(i,k)$. The two encoded functions therefore agree at every coordinate, proving the identity.

**Key facts.** `FABL.binaryExtensionEncode_basisVector`.
