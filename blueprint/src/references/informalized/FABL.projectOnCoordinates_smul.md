<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/GeneralizedFourierFormulas.lean :: FABL.projectOnCoordinates_smul -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Homogeneity of Coordinate Projection

**Claim.** For every real scalar $c$ and function $f$ on the product space, the coordinate projection satisfies $P_J(cf)=cP_Jf$.

**Proof.** Evaluate both sides at an arbitrary input $x$. By definition, the left side is the expectation over the product probability mass function of $y\mapsto c f(\operatorname{merge}_J(x,y))$. Pulling the constant scalar $c$ out of this finite expectation gives $c$ times the expectation of $y\mapsto f(\operatorname{merge}_J(x,y))$, which is exactly the right side at $x$. Since this holds for every $x$, the two functions agree.

**Key facts.** `FABL.pmfExpectation_const_mul`.
