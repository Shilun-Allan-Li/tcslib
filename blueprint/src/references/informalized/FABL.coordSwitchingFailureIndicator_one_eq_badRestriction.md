<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Switching.lean :: FABL.coordSwitchingFailureIndicator_one_eq_badRestriction -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Failure Indicator and Bad Restrictions

**Claim.** For a disjunctive normal form and coordinate restriction, the failure indicator at threshold $1$ equals $1$ if the restricted function takes different values on some pair of Boolean inputs, and equals $0$ otherwise.

**Proof.** The decision-tree depth is at least $1$ exactly when the function is nonconstant, that is, when there are inputs $x,y$ on which its values differ (\texttt{FABL.one_le_decisionTreeDepth_iff_nonconstant}). Apply this to the restricted function. Its nonconstancy condition is precisely the definition of a bad restriction. Since the indicator at threshold $1$ is $1$ exactly when that depth is at least $1$, it equals $1$ for a bad restriction and $0$ otherwise.

**Key facts.** `FABL.one_le_decisionTreeDepth_iff_nonconstant`.
