<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/KrawtchoukPolynomials.lean :: FABL.krawtchoukSummand_leadingCoeff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Leading coefficient of a Krawtchouk summand

**Claim.** The leading coefficient of the $k$th summand in the defining sum for the Krawtchouk polynomial of parameters $n,j$ is $(-1)^k(k!)^{-1}((j-k)!)^{-1}(-1)^{j-k}$.

**Proof.** The summand is a product of scalar factors and two polynomial factors. The leading coefficient of a product is the product of the leading coefficients. The first polynomial factor has leading coefficient $(k!)^{-1}$ (`chooseFactor_leadingCoeff`); the complementary factor, formed by composing the descending factorial with $n-X$ and scaling by $((j-k)!)^{-1}$, has leading coefficient $((j-k)!)^{-1}(-1)^{j-k}$ (`complementChooseFactor_leadingCoeff`). Including the scalar factor $(-1)^k$ and multiplying these quantities gives the stated expression.

**Key facts.** `FABL.chooseFactor_leadingCoeff`, `FABL.complementChooseFactor_leadingCoeff`.
