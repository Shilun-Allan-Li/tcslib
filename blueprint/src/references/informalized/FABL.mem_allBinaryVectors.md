<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/ExecutableFiniteFields.lean :: FABL.mem_allBinaryVectors -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Every Binary Vector Appears

**Claim.** Every vector in $(\mathbb Z/2\mathbb Z)^\ell$ occurs in the recursively constructed list of binary vectors.

**Proof.** Proceed by induction on $\ell$. In dimension zero, there is only the zero-dimensional vector, so it is the sole list entry. For the induction step, the first coordinate of a given vector is either $0$ or $1$ (\texttt{f₂\_eq\_zero\_or\_one}). Its remaining coordinates form the tail, which occurs in the preceding-dimensional list by induction. If the first coordinate is $0$, prefixing the tail places the vector in the first mapped list in the concatenation; if it is $1$, prefixing the tail places it in the second mapped list. In either case the original vector occurs.

**Key facts.** `FABL.f₂_eq_zero_or_one`.
