<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/ProductLTFNoiseCorrection.lean :: FABL.productProbabilityPMF_bind_coordinates -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Coordinatewise binding of product distributions

**Claim.** Binding the product law of $n$ independent samples from $p$ to the coordinatewise laws $q(a)$ gives the product law whose common coordinate law is the mixture of $q(a)$ over $p$.

**Proof.** Apply the coordinatewise binding formula for independent products (\texttt{independentProductPMF\_bind\_coordinates}) to the family in which every coordinate has law $p$, and where the output law at each coordinate, given input $a$, is $q(a)$. The formula says that binding these product laws produces the independent product of the coordinatewise mixtures $p.bind\,q$. Since this input and output law is the same at every coordinate, that product is exactly the stated product probability distribution.

**Key facts.** `FABL.independentProductPMF_bind_coordinates`.
