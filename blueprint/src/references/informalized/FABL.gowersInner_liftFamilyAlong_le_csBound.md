<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Gowers.lean :: FABL.gowersInner_liftFamilyAlong_le_csBound -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Cauchy–Schwarz Bound for a Lift

**Claim.** The Gowers inner product of a family lifted along an embedding is at most its recursively defined Cauchy–Schwarz bound.

**Proof.** Proceed by induction on the dimension $r$ of the family being lifted. When $r=0$, the lifted family is constant in its cube index: there is no input coordinate to restrict. Its inner product is therefore the diagonal inner product of $F(0)$, exactly the dimension-zero Cauchy–Schwarz bound. Now suppose the result holds in dimension $r$, and consider a family of dimension $r+1$. Let $e'$ be the restriction of the embedding to the first $r$ coordinates, and let $F_0,F_1$ be the two families obtained by appending respectively $0$ and $1$ to each input. The Cauchy–Schwarz inequality at coordinate $e(r)$ bounds the lifted inner product by the product of the square roots of the inner products of its two duplications. The duplication-of-a-lift identity (FABL.gowersDuplicateAt_liftFamilyAlong) identifies these two families as the lifts of $F_0,F_1$ along $e'$. Apply the induction hypothesis to each, then use monotonicity of the square root on nonnegative inputs and monotonicity of multiplication for nonnegative factors. The result is the product of the square roots of the two corresponding recursive bounds, which is precisely the successor definition of the Cauchy–Schwarz bound.

**Key facts.** `FABL.gowers_cauchy_schwarz_at`, `FABL.gowersDuplicateAt_liftFamilyAlong`.
