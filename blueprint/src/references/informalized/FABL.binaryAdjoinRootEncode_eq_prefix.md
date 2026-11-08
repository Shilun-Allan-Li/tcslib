<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/ExecutableFiniteFields.lean :: FABL.binaryAdjoinRootEncode_eq_prefix -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Encoding as a root-power sum

**Claim.** The encoding of $y$ in the quotient algebra is the sum of its coordinates times the corresponding powers of the adjoined root, from index $0$ through $ell-1$.

**Proof.** Expand the low-coefficient polynomial of $y$ as the sum of its coefficients times powers of $X$, and map that polynomial into the quotient algebra. The map sends each coefficient constant to the same scalar in the algebra and sends $X$ to the adjoined root, so the result is the sum of $y_i$ times the corresponding root powers. For each index $i<\ell$, the coefficient-at-index function returns precisely $y_i$. Reindexing the finite sum over indices of length $\ell$ as a sum over $0\le i<\ell$ gives the stated prefix sum.
