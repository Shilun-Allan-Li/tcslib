<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/ProductLTFNoiseCorrection.lean :: FABL.independentProductPMF_bind_coordinates -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Coordinatewise binding of an independent product

**Claim.** Sampling an independent product and then sampling each output coordinate according to its kernel gives the independent product of the coordinatewise bound distributions.

**Proof.** Fix an output tuple $y$ and compare its point probabilities. The probability that the two-stage sampling produces $y$ is the finite sum over input tuples $x$ of the input probability times the conditional output probability. The point-probability formula for an independent product (\texttt{FABL.independentProductPMF_apply}) writes these probabilities as products over coordinates. Expanding the finite sum over all tuples as an iterated sum over the coordinates, and rearranging the finite products, factors the result into the product over $i$ of $\sum_{x_i} p_i(x_i)q_i(x_i)(y_i)$. Each factor is the point probability at $y_i$ of the distribution obtained by binding $p_i$ with $q_i$. Thus the point probabilities agree with those of the independent product of these coordinatewise distributions, so the distributions are equal.

**Key facts.** `FABL.independentProductPMF_apply`.
