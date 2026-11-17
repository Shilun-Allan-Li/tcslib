<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/ProductLTFNoiseCorrection.lean :: FABL.independentProductPMF_map_coordinates -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Coordinatewise mapping of an independent product

**Claim.** Mapping each coordinate of an independent product through its corresponding function gives the independent product of the coordinatewise mapped distributions.

**Proof.** Fix an output tuple $y$. Its probability under the mapped distribution is the sum, over all input tuples $x$ mapping to $y$, of the input point probabilities. The point-probability formula for an independent product (\texttt{FABL.independentProductPMF_apply}) expresses each input probability as a product of coordinate probabilities. The finite sum over tuples can be expanded as an iterated coordinate sum; the condition that $x$ maps to $y$ is exactly the collection of conditions $f_i(x_i)=y_i$. Consequently the sum factors as the product over $i$ of the sum of $p_i(x_i)$ over inputs with $f_i(x_i)=y_i$. These factors are the point probabilities of the coordinatewise mapped distributions, which proves the equality.

**Key facts.** `FABL.independentProductPMF_apply`.
