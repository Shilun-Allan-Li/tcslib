<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/DecisionTreeInequalities.lean :: FABL.pmfExpectation_productMean_fixProductCoordinate -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Mean Under Coordinate Fixing

**Claim.** For any coordinate $j$, averaging the product mean of $f$ with coordinate $j$ fixed over the fixed value gives the product mean of $f$.

**Proof.** Expand both product means as expectations. The left side averages first over the fixed value $\omega\sim\pi$ and then over a product sample $x$. Since these are finite expectations, they may be interchanged (`pmfExpectation_comm`). For each fixed $x$, the resulting inner average over $\omega$ is the value of the coordinate projection at $x$ (`coordinateProjection_apply`). Hence the expression is the product mean of that projection. The projection here averages over all coordinates except $j$, namely the projection onto the set of coordinates $\operatorname{univ}\setminus\{j\}$. The basis assumption gives that projecting onto any set of coordinates preserves product mean (`FiniteFourierBasis.productMean_projectOnCoordinates`), so this is the product mean of $f$.

**Key facts.** `FABL.pmfExpectation_comm`, `FABL.coordinateProjection_apply`, `FABL.FiniteFourierBasis.productMean_projectOnCoordinates`.
