<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/GeneralizedFourierFormulas.lean :: FABL.projectOnCoordinates_add -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Additivity of Coordinate Projection

**Claim.** The coordinate projection onto $J$ is additive: $P_J(f+g)=P_Jf+P_Jg$.

**Proof.** Evaluate both sides at an arbitrary input $x$. By definition, the left side is the expectation over a random product input $y$ of $(f+g)$ evaluated at the vector obtained by keeping $x$ on $J$ and using $y$ off $J$. Pointwise, evaluation of $f+g$ is the sum of the evaluations of $f$ and $g$. Linearity of the finite probability expectation (\texttt{FABL.pmfExpectation_add}) therefore identifies this with the sum of the two separate projected values at $x$. Since this holds for every $x$, the functions are equal.

**Key facts.** `FABL.pmfExpectation_add`.
