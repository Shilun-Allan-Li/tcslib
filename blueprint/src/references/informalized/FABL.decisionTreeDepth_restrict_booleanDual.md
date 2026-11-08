<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Switching.lean :: FABL.decisionTreeDepth_restrict_booleanDual -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Depth under duality and restriction

**Claim.** For every assignment of coordinate states, the restriction of the dual function has the same minimum decision tree depth as the restriction of the original function with fixed signs interchanged.

**Proof.** First, identify the restricted dual with the binary dual of the restriction of $f$ under the assignment with its fixed states interchanged. This is the restriction identity (`FABL.CoordRestriction.restrict_booleanDual`): negating the input sign vector swaps the fixed signs and complements each free binary input, while the outer negation in the definition of the dual supplies the other sign change. The claimed depth equality now follows from invariance of minimum decision tree depth under binary duality (`FABL.decisionTreeDepth_binaryBooleanDual`).

**Key facts.** `FABL.CoordRestriction.restrict_booleanDual`, `FABL.decisionTreeDepth_binaryBooleanDual`.
