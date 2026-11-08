<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/CSPTesterExamples.lean :: FABL.blrCSPConstraint_eq_distinct_of_not_collision -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# BLR constraint without collisions

**Claim.** When $x$ and $y$ are nonzero and distinct, the constraint assigned to $(x,y)$ is the linear equation with right-hand side zero on the three queries $x$, $y$, and $x+y$, in that order.

**Proof.** The hypothesis that the queries do not collide is exactly the negation of the condition that $x=0$, $y=0$, or $x=y$. In the definition of the constraint, the noncollision branch assigns the predicate of arity three with right-hand side zero and the scope given by the ordered BLR query triple $(x,y,x+y)$. Unfolding that definition in this branch gives the stated constraint.
