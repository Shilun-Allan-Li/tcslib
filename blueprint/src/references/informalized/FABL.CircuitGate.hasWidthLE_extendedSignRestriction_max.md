<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/CircuitInfluence.lean :: FABL.CircuitGate.hasWidthLE_extendedSignRestriction_max -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Width bounded by family depth

**Claim.** For any chosen gate and family member, the restriction of that function has width at most the maximum restricted decision-tree depth over the family.

**Proof.** The gate representation theorem says that every Boolean function has a representation in the normal form associated with the gate whose width is at most its decision-tree depth (`CircuitGate.hasWidthLE_decisionTreeDepth`). Apply it to the chosen restricted function, using the identification of its restricted depth with the decision-tree depth of its binary encoding. The restricted depth of this family member is at most the maximum restricted depth over all members (`restrictedDecisionTreeDepth_le_max`). Increasing the width bound preserves the representation, by monotonicity (`CircuitGate.hasWidthLE_mono`), giving the claimed bound.

**Key facts.** `FABL.CircuitGate.hasWidthLE_mono`, `FABL.restrictedDecisionTreeDepth_le_max`.
