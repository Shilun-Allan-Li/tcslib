<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/QuadraticPCPP.lean :: FABL.satisfiesHomogeneousQuadraticSystem_zero_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Zero-Dimensional Quadratic Systems

**Claim.** For a system of homogeneous quadratic equations in zero variables and the unique assignment on the empty variable set, that assignment satisfies every equation exactly when every equation has right-hand side $0$.

**Proof.** We prove both implications equation by equation. If the assignment satisfies every equation in the list, then each listed equation is satisfied by the unique empty assignment; the zero-dimensional equation criterion says that its right-hand side must be $0$ (`FABL.homogeneousQuadraticEquation_satisfiedBy_zero_iff`). Conversely, if every listed equation has right-hand side $0$, that same criterion implies that each is satisfied by the empty assignment. Hence the assignment satisfies the whole system.

**Key facts.** `FABL.homogeneousQuadraticEquation_satisfiedBy_zero_iff`.
