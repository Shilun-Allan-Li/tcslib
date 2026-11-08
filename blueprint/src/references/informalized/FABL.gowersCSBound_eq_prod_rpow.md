<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Gowers.lean :: FABL.gowersCSBound_eq_prod_rpow -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Product Formula for the Cauchy–Schwarz Bound

**Claim.** For positive $k$, every $r\geq0$, and every family $F$ indexed by the $r$-dimensional Boolean cube, the recursive Cauchy–Schwarz bound equals the product over that cube of the diagonal inner products raised to the power $1/2^r$.

**Proof.** Proceed by induction on $r$. When $r=0$, the zero-dimensional cube has one point, so the product has a single factor. Its exponent is $1$, and the recursive bound is the diagonal inner product at that unique point; hence the formula holds. For the step from $r$ to $r+1$, the recursive definition splits the bound into the product of square roots of the bounds for the two slices of $F$, obtained by fixing the last coordinate to $0$ or $1$. Apply the induction hypothesis to each slice, then use the square-root product identity (\texttt{FABL.sqrt_prod_gowersDiagonal_rpow}) to halve the exponent in each product. Finally, the Boolean-cube product decomposition (\texttt{FABL.prod_f₂Cube_succ}) says that the product over the full $(r+1)$-cube is the product over these two slices, giving the claimed formula.

**Key facts.** `FABL.sqrt_prod_gowersDiagonal_rpow`, `FABL.prod_f₂Cube_succ`.
