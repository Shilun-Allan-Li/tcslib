<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/RestrictedWeightAlgorithm.lean :: FABL.fourierCoeff_reindexedSignRestriction -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourier coefficients of reindexed sign restrictions

**Claim.** For a Boolean target function, a fixed assignment outside $J$, and a subset $T$ of the reindexed free coordinates, the Fourier coefficient of the resulting function on the $J$-coordinates equals the indexed Fourier coefficient of the restriction at the image of $T$ under the inverse enumeration of $J$.

**Proof.** The equivalence from the cube of dimension $|J|$ to assignments on $J$ changes variables in the uniform expectation. Under this change, the character indexed by $T$ becomes the indexed character on the image of $T$ under the inverse enumeration, since the product over coordinates is preserved by the bijection. The function being averaged becomes the target evaluated at the combined free assignment and fixed outside assignment. This is exactly the indexed Fourier coefficient of the restriction at the stated image.
