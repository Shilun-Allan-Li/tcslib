<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/GotsmanLinialExtremizer.lean :: FABL.natDegree_gotsmanLinialPolynomial -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Degree of the Gotsman–Linial Polynomial

**Claim.** For every pair of natural numbers $n,k$, the Gotsman–Linial polynomial formed from the specified $k$ linear factors has natural degree $k$.

**Proof.** The polynomial is the product, over the $k$ indices in the range, of factors of the form $X-c$, with each $c$ a real constant. The degree of a finite product of such linear factors is the number of factors (`Polynomial.natDegree_finsetProd_X_sub_C_eq_card`). The range has cardinality $k$, so the natural degree is $k.
