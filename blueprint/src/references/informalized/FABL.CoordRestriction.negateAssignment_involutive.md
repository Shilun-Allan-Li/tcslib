<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Switching.lean :: FABL.CoordRestriction.negateAssignment_involutive -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Involutivity of Assignment Negation

**Claim.** Negating every state in an assignment twice returns the original assignment.

**Proof.** Two assignments are equal if they agree at every coordinate. Fix a coordinate $i$. Evaluating the twice-negated assignment there applies state negation twice to $\rho(i)$, which returns $\rho(i)$: the free state stays free, while the two fixed states are exchanged and then exchanged back. Thus the assignments agree at every coordinate.
