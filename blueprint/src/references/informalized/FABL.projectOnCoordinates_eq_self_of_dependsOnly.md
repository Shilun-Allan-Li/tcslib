<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/GeneralizedFourierFormulas.lean :: FABL.projectOnCoordinates_eq_self_of_dependsOnly -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Projection Fixes Coordinate-Dependent Functions

**Claim.** If $f$ depends only on coordinates in $J$, then its projection onto $J$ equals $f$.

**Proof.** Fix an input $x$. In the projection, each vector formed by retaining $x$ on $J$ and filling the other coordinates from an arbitrary input $y$ agrees with $x$ on every coordinate in $J$. Since $f$ depends only on those coordinates, its value on every such vector is $f(x)$. The expectation being taken is therefore the expectation of the constant function with value $f(x)$, which equals $f(x)$ by the constant-expectation identity (\texttt{FABL.pmfExpectation_const}). This holds at every $x$, proving equality of the functions.

**Key facts.** `FABL.pmfExpectation_const`.
