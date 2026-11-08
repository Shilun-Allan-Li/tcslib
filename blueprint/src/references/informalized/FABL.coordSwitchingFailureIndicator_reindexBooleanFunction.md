<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Switching.lean :: FABL.coordSwitchingFailureIndicator_reindexBooleanFunction -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Reindexing the Failure Indicator

**Claim.** Reindexing a Boolean function along a bijection and then restricting it gives the same switching failure indicator as restricting the original function by the correspondingly reindexed coordinate assignment.

**Proof.** The decision-tree depth of the restriction of the reindexed function equals the depth of the original function restricted by $i\mapsto\rho(e(i))$ (\texttt{FABL.restrictedDecisionTreeDepth_reindexBooleanFunction}). The failure indicators compare these depths with the same threshold $k$, so the indicators agree.

**Key facts.** `FABL.restrictedDecisionTreeDepth_reindexBooleanFunction`.
