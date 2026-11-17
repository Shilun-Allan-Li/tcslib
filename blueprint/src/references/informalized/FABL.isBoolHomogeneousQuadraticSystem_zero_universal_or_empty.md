<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/QuadraticPCPP.lean :: FABL.isBoolHomogeneousQuadraticSystem_zero_universal_or_empty -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Zero-Dimensional Quadratic Systems

**Claim.** For a finite system of homogeneous quadratic equations in zero variables, either every Boolean assignment on the empty coordinate set satisfies the system, or none does.

**Proof.** The zero-dimensional result for binary-vector assignments says that the system is either satisfied by every such vector or by none ( `homogeneousQuadraticSystem_zero_universal_or_empty`). In the first case, convert any Boolean assignment to its binary vector and apply the universal property. In the second case, if a Boolean assignment satisfied the system, its converted vector would satisfy it too, contradicting the empty case. Thus the same alternative holds for Boolean assignments.

**Key facts.** `FABL.homogeneousQuadraticSystem_zero_universal_or_empty`.
