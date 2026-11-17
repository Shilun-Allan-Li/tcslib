<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Switching.lean :: FABL.coordSwitchingFailureIndicator_booleanDual -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Switching Failure under Boolean Duality

**Claim.** The switching failure indicator of the Boolean dual at threshold $k$ and assignment $\rho$ equals that of the original function at threshold $k$ and assignment $-\rho$.

**Proof.** The decision-tree depth of the restriction of the Boolean dual under $\rho$ equals the depth of the restriction of the original function under the negated assignment (\texttt{FABL.decisionTreeDepth_restrict_booleanDual}). By definition, the indicator is $1$ exactly when this depth is at least $k$, and is $0$ otherwise. Equal depths therefore give equal indicators.

**Key facts.** `FABL.decisionTreeDepth_restrict_booleanDual`.
