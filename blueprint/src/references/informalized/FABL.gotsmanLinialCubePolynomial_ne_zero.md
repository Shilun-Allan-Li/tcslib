<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/GotsmanLinialExtremizer.lean :: FABL.gotsmanLinialCubePolynomial_ne_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Nonvanishing of the Cube Polynomial

**Claim.** For every $n,k$ and sign vector $x$, the value of the cube polynomial at the coordinate sum is nonzero.

**Proof.** Use the product formula to express the value as a product, over $j<k$, of the coordinate sum minus the corresponding root. Each such factor is nonzero by the nonvanishing-of-an-individual-factor result ($\texttt{gotsmanLinial_factor_ne_zero}$). A finite product of nonzero real numbers is nonzero, proving the claim. When $k=0$, the product is empty and equals $1$, so the conclusion still holds.

**Key facts.** `FABL.gotsmanLinialCubePolynomial_eq_product`, `FABL.gotsmanLinial_factor_ne_zero`.
