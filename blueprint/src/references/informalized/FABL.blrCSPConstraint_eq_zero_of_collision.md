<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/CSPTesterExamples.lean :: FABL.blrCSPConstraint_eq_zero_of_collision -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Collision Constraints Have Zero Scope

**Claim.** Whenever the BLR queries collide, the associated CSP constraint is the one-variable zero equation with scope at the zero vector.

**Proof.** By definition, the constraint is chosen by splitting on whether the queries collide. Under the stated collision hypothesis, the collision branch applies, and that branch is exactly the one-variable predicate with right-hand side zero and scope at the zero vector. The two constraints therefore agree.
