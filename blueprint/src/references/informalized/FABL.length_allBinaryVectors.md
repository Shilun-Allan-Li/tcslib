<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/ExecutableFiniteFields.lean :: FABL.length_allBinaryVectors -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Number of binary vectors

**Claim.** For every nonnegative integer $\ell$, the list of all binary vectors of length $\ell$ over $\mathbb F_2$ has length $2^\ell$.

**Proof.** Proceed by induction on $\ell$. At length zero, the list consists of the single empty vector, so its length is $1=2^0$. At length $\ell+1$, the construction appends a leading zero or a leading one to each vector of length $\ell$. Each mapped list therefore has the same length as the original, and concatenation adds the two lengths. By induction this gives $2^\ell+2^\ell=2^{\ell+1}$.
