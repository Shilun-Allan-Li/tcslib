<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Gowers.lean :: FABL.gowersCSBound_eq_prod_norm -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Cauchy–Schwarz Bound as a Product of Norms

**Claim.** For $k>0$, the recursively defined Cauchy–Schwarz bound at level $k$ equals the product over $s\in\mathbb F_2^k$ of the Gowers norms of the corresponding functions.

**Proof.** Apply the product formula for the recursive bound (\texttt{FABL.gowersCSBound_eq_prod_rpow}) at level $k$. Each factor in that formula is the diagonal Gowers inner product raised to the reciprocal of $2^k$, which is exactly the definition of the corresponding Gowers norm. Thus the two products agree.

**Key facts.** `FABL.gowersCSBound_eq_prod_rpow`.
