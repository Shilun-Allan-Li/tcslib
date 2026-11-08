<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/OracleNondeterministic.lean :: Turing.OracleTM.toOracleNDTM_wellFormed -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Preservation of well-formedness

**Claim.** If the query state and the two answer states of an oracle machine are pairwise distinct, the nondeterministic oracle machine obtained from it has the same pairwise distinctness property.

**Proof.** The conversion retains the query state and both answer states. Therefore each of the three inequalities required for well-formedness of the nondeterministic machine is exactly the corresponding inequality supplied by the original machine's well-formedness hypothesis.
