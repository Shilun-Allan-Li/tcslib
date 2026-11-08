<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/HastadThreeSat.lean :: FABL.expect_boolChoices_prod -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Product average for Boolean choices

**Claim.** For independent uniform Boolean coordinates, the average of the product of the selected coordinate functions equals the product of their individual averages.

**Proof.** Extend each coordinate factor to all coordinates by setting $q_i(b)=a_i(b)$ when $i\in S$ and $q_i(b)=1$ otherwise. Then the product over $S$ is the product over all coordinates of $q_i(\sigma_i)$. Independence of uniform coordinates makes the average of this product the product of the coordinate averages (`expect_prod_finArrow`). For $i\in S$, the average over the two Boolean values is $(a_i(\mathrm{false})+a_i(\mathrm{true}))/2$; for $i\notin S$, it is $1$. Multiplying these factors gives the claimed product over $S$.

**Key facts.** `FABL.expect_prod_finArrow`.
