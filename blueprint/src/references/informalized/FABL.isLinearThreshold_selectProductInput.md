<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/ProductLTFNoise.lean :: FABL.isLinearThreshold_selectProductInput -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Selected inputs preserve threshold form

**Claim.** Restricting a product-domain linear threshold function to two selected values at each coordinate gives a linear threshold function on the Boolean cube.

**Proof.** Write the original threshold as $a_0+\sum_i a_i(x_i)$, where each $a_i$ is a real-valued score on the product alphabet. For each coordinate, the score at the selected value is the midpoint of the two selected scores plus their half-difference multiplied by the sign of the Boolean input (\texttt{selectedScore\_eq\_midpoint\_add\_difference}). Summing these identities expresses the restricted score as a constant, namely $a_0+\sum_i (a_i(u_i^+)+a_i(u_i^-))/2$, plus a linear Boolean score with coefficient $(a_i(u_i^+)-a_i(u_i^-))/2$ at coordinate $i$. Applying the same threshold-sign rule proves the restricted function is a linear threshold function.

**Key facts.** `FABL.selectedScore_eq_midpoint_add_difference`.
