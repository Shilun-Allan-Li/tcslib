<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/ExecutableFiniteFields.lean :: FABL.length_binaryVectorPairs -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Number of ordered binary vector pairs

**Claim.** For every nonnegative integer $\ell$, the list of ordered pairs of binary vectors of length $\ell$ has length $2^{2\ell}$.

**Proof.** The ordered-pair list is the product of the list of all binary vectors of length $\ell$ with itself. Its length is therefore the square of the length of that vector list. Since that list has length $2^\ell$ (\texttt{length_allBinaryVectors}), the pair list has length $(2^\ell)^2=2^{\ell+\ell}=2^{2\ell}$.

**Key facts.** `FABL.length_allBinaryVectors`.
