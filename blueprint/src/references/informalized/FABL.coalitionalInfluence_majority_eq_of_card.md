<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/CoalitionalInfluenceAsymptotics.lean :: FABL.coalitionalInfluence_majority_eq_of_card -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Majority Influence Depends on Set Size

**Claim.** If coordinate sets $A$ and $B$ have the same cardinality, then the majority function has equal coalitional influence on $A$ and $B$.

**Proof.** Write the coalitional influence on each set as the sum of the two directional influences, toward $1$ and toward $-1$, using `FABL.coalitionalInfluence_eq_toward_add_toward`. For each target sign separately, equal cardinality of $A$ and $B$ implies equality of their directional influences by `FABL.coalitionalInfluenceToward_majority_eq_of_card`. Adding these two equalities proves the claim.

**Key facts.** `FABL.coalitionalInfluence_eq_toward_add_toward`, `FABL.coalitionalInfluenceToward_majority_eq_of_card`.
