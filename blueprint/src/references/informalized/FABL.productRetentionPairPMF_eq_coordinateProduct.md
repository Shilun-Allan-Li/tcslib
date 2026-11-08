<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/ProductLTFNoiseCorrection.lean :: FABL.productRetentionPairPMF_eq_coordinateProduct -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Coordinatewise product representation

**Claim.** The joint law obtained by sampling an initial sequence from the product law and then applying independent coordinate noise is the law obtained by independently sampling coordinate retention-and-resampling pairs and regrouping their entries into two sequences.

**Proof.** Equality of the two probability mass functions can be checked at an arbitrary pair of sequences $(x,y)$. Under the first construction, the mass of $(x,y)$ is the mass of $x$ times the conditional noise mass of $y$ given $x$ (the product pair mass formula, `productRetentionPairPMF_apply`). The product law formula (`productProbabilityPMF_apply`) makes this $(\prod_i \pi(x_i))$ times the noise-kernel mass. By independence across coordinates, this is the product over $i$ of $\pi(x_i)$ times the one-coordinate noise mass from $x_i$ to $y_i$. The one-coordinate pair mass formula (`productRetentionCoordinatePairPMF_apply`) identifies each factor with the mass of $(x_i,y_i)$ under the coordinate retention-and-resampling pair law. Thus the mass equals the product mass assigned to the coordinate pairs, which is precisely the mass of the regrouped law. The coordinate equivalence bijects pairs of sequences with sequences of coordinate pairs, so all other points contribute zero to the mapped law.

**Key facts.** `FABL.productRetentionPairPMF_apply`, `FABL.productProbabilityPMF_apply`, `FABL.productRetentionCoordinatePairPMF_apply`.
