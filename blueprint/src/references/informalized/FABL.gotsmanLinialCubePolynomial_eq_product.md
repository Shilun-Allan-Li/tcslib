<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/GotsmanLinialExtremizer.lean :: FABL.gotsmanLinialCubePolynomial_eq_product -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Cube Polynomial Product Formula

**Claim.** For each sign vector, evaluating the polynomial whose factors are $X$ minus the specified roots equals the product of the corresponding differences between the coordinate sum and those roots.

**Proof.** Fix a sign vector $x$. The polynomial is a finite product of linear factors. Evaluation at the sum of the signs preserves finite products, and evaluating each factor $X-C(r)$ gives the coordinate sum minus $r$. Applying this to each factor identifies the polynomial value with the stated product.
