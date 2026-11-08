<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/BPOperator.lean :: Randomized.BPdot_P_eq_BPP_PTM -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Randomized polynomial time via reductions

**Claim.** The class of languages that reduce by a many-one reduction to some language in P equals the union, over natural numbers $c$, of the classes decidable by bounded-error randomized machines in time bounded by a constant multiple of $n\mapsto n^c+1$.

**Proof.** Rewrite the reduction closure of P using the characterization of randomized reductions to P as BPP (\texttt{Randomized.BPdot_P_eq_BPP}). Then rewrite BPP as the stated union of randomized time classes (\texttt{Randomized.BPP_PTM_eq}). The two equalities yield the result.

**Key facts.** `Randomized.BPdot_P_eq_BPP`, `Randomized.BPP_PTM_eq`.
