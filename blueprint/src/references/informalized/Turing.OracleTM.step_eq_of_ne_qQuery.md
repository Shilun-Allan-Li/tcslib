<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Oracle.lean :: Turing.OracleTM.step_eq_of_ne_qQuery -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Step Independence Away from the Query State

**Claim.** If the configuration is not in the query state, one step from it is the same for either oracle language.

**Proof.** Split according to whether the configuration state is empty or is some state $q$. In the empty-state case, a step leaves the configuration unchanged for either oracle. In the other case, the assumption that the configuration is not in the query state implies $q\ne qQuery$. Therefore the transition branch, rather than the oracle-query branch, is taken for both languages, and it uses the same machine transition and configuration data. The resulting configurations are equal.
