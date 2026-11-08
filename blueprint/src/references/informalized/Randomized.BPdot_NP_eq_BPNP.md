<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/BPOperator.lean :: Randomized.BPdot_NP_eq_BPNP -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Randomized reductions from NP

**Claim.** The class of languages that reduce by a many-one reduction to some language in NP equals the class of languages that reduce by a many-one reduction to 3-SAT.

**Proof.** For one inclusion, suppose a language reduces to an NP language $C$. Since 3-SAT is NP-hard, $C$ reduces to 3-SAT (\texttt{Complexity.SAT3_NPHard}); composing the two reductions yields a reduction from the original language to 3-SAT (\texttt{Randomized.RandReducible.of_polyTimeReducible_right}). For the reverse inclusion, 3-SAT itself belongs to NP (\texttt{Complexity.SAT3_mem_NP}), so any language reducing to 3-SAT already reduces to some language in NP. Hence the two reduction classes coincide.

**Key facts.** `Complexity.SAT3_NPHard`, `Randomized.RandReducible.of_polyTimeReducible_right`, `Complexity.SAT3_mem_NP`.
