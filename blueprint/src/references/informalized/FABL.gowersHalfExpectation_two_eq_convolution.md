<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Gowers.lean :: FABL.gowersHalfExpectation_two_eq_convolution -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Half Expectation as Convolution

**Claim.** The half expectation for a family indexed by pairs of bits, with the last index fixed to $b$, equals the normalized additive convolution of the functions indexed by $(0,b)$ and $(1,b)$, evaluated at $y(0)$.

**Proof.** By the convolution formula (FABL.convolution_apply_add), the right-hand side is the average over a cube point $z$ of the product of the two functions at $z$ and at $y(0)+z$. The half expectation first averages over $x$, and its product ranges over the two possible values of the remaining bit. Splitting that product according to those values gives the same two factors: the zero slice is evaluated at $x$, and the one slice at $x+y(0)$. The identification of each inserted pair with $(0,b)$ or $(1,b)$ follows from the definition of the pair and insertion. Thus the integrands agree pointwise, and both averages use the uniform cube measure. The split of the product over the Boolean cube into its two slices is the product decomposition (FABL.prod_f₂Cube_succ).

**Key facts.** `FABL.convolution_apply_add`, `FABL.prod_f₂Cube_succ`.
