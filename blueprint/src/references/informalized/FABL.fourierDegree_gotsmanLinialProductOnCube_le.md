<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/GotsmanLinialExtremizer.lean :: FABL.fourierDegree_gotsmanLinialProductOnCube_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Degree of the cube product polynomial

**Claim.** The product over $j=0,\ldots,d-1$ of the factors $\sum_{i=0}^{n-1}x_i-(2(a+j)-n+1)$ has Fourier degree at most $d$.

**Proof.** Proceed by induction on $d$. When $d=0$, the empty product is the constant function $1$. For a set $S$ with $|S|>0$, its coefficient is the expectation of the monomial indexed by $S$, which is zero because every nonempty monomial has mean zero (`expect_monomial`). The degree criterion (`fourierDegree_le_iff`) gives degree zero. For the induction step, factor the product with $d+1$ terms into the product with $d$ terms times the final factor, whose form is a coordinate sum minus a real constant. The induction hypothesis bounds the first product's degree by $d$. Multiplication by this factor raises the degree bound by at most one (`fourierDegree_mul_coordinateSum_sub_le`), giving the bound $d+1$.

**Key facts.** `FABL.fourierDegree_le_iff`, `FABL.expect_monomial`, `FABL.fourierDegree_mul_coordinateSum_sub_le`.
