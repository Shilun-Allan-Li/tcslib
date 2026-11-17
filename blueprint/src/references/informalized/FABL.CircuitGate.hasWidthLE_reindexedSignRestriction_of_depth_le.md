<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/LMN.lean :: FABL.CircuitGate.hasWidthLE_reindexedSignRestriction_of_depth_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Width from restricted decision-tree depth

**Claim.** If the restriction of a function, reindexed on the free coordinates, has decision-tree depth at most $\ell$, then it has width at most $\ell$ in the normal form associated with either gate.

**Proof.** The gate representation theorem gives the reindexed restricted function a CNF when the gate is AND, or a DNF when it is OR, with width at most that function's decision-tree depth (`CircuitGate.hasWidthLE_decisionTreeDepth`). The restricted decision-tree depth in the hypothesis is the same depth after reindexing the free coordinates (`restrictedDecisionTreeDepth_eq_reindexedSignRestriction`). Thus the representation has width at most the restricted depth, which is at most $\ell$. Monotonicity of representation width then raises the bound to $\ell$ (`CircuitGate.hasWidthLE_mono`).

**Key facts.** `FABL.CircuitGate.hasWidthLE_mono`, `FABL.CircuitGate.hasWidthLE_decisionTreeDepth`, `FABL.restrictedDecisionTreeDepth_eq_reindexedSignRestriction`.
