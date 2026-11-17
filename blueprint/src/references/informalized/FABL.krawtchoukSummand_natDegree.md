<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/KrawtchoukPolynomials.lean :: FABL.krawtchoukSummand_natDegree -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Degree of a Krawtchouk summand

**Claim.** For natural numbers $n,j,k$ with $k\le j$, the natural degree of the $k$th summand in the defining sum for the Krawtchouk polynomial of parameters $n,j$ is $j$.

**Proof.** The two polynomial factors in the summand are nonzero: each has a positive leading coefficient, as given by `chooseFactor_leadingCoeff` and `complementChooseFactor_leadingCoeff`. The scalar factor $(-1)^k$ is also nonzero. Thus the degree of their product is the sum of their degrees. The first factor has degree $k$ (`chooseFactor_natDegree`), and the complementary factor has degree $j-k$ (`complementChooseFactor_natDegree`). Since $k\le j$, these add to $j$, proving the claim.

**Key facts.** `FABL.chooseFactor_leadingCoeff`, `FABL.complementChooseFactor_leadingCoeff`, `FABL.chooseFactor_natDegree`, `FABL.complementChooseFactor_natDegree`.
