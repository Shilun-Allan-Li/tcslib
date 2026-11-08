<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/UniqueGamesReduction.lean :: FABL.RegularUniqueGame.edgeError_eq_one_sub_value -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Edge error and constraint value

**Claim.** The average edge error of a labeling equals one minus the value of the associated finite unique-game constraint instance under that labeling.

**Proof.** First identify the edge error with the average unsatisfied-constraint indicator. The regular game’s neighborhood average equals its directed-edge average by `FABL.RegularUniqueGame.edgeExpectation_eq_neighborhoodExpectation`. Each directed edge is an occurrence in the associated finite game; its unsatisfied indicator is exactly the edge-failure indicator. Indeed, the constraint is satisfied precisely when the permutation sends the target label to the source label (`FABL.FiniteUniqueGame.constraint_satisfied_iff`), so both indicators are zero on satisfied edges and one otherwise. Reindexing by the edge correspondence therefore identifies the edge error with the average unsatisfied cost. The total unsatisfied cost is the sum of the unsatisfied indicators (`FABL.CSPInstance.unsatisfiedCost_eq_sum`), and the finite uniform average is that sum divided by the number of constraints. Finally, the value is one minus this normalized unsatisfied cost (`FABL.CSPInstance.value_eq_one_sub_unsatisfiedCost_div`); rearranging gives the asserted identity.

**Key facts.** `FABL.RegularUniqueGame.edgeExpectation_eq_neighborhoodExpectation`, `FABL.FiniteUniqueGame.constraint_satisfied_iff`, `FABL.CSPInstance.unsatisfiedCost_eq_sum`, `FABL.CSPInstance.value_eq_one_sub_unsatisfiedCost_div`.
