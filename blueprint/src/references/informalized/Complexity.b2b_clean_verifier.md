<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Inclusions.lean :: Complexity.b2b_clean_verifier -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial-Time Clean Verifier

**Claim.** For a language $V$ in polynomial time, there are natural numbers $e,c_V$ and a finite Boolean Turing machine $M_V$ whose clean simulation halts on every word $y$ with output the indicator of membership in $V$, blank work tapes, heads at the origin, and head positions bounded by $c_V(|y|^e+1)$.

**Proof.** Since $V$ is in polynomial time, it is in polynomial space (`Complexity.P_subset_PSPACE`). Unpacking that space bound provides an exponent $e$, a coefficient $c_V$, and a finite machine $M_V$ that decides $V$ within the corresponding polynomial space bound. For each input word $y$, this gives a computation with output equal to the membership indicator and space at most $c_V(|y|^e+1)$. Apply the clean simulation result (`Complexity.b2b_clean_run`) to that computation and space bound. It yields a run that halts with the same output, clears all work-tape cells, returns every work-tape head to the origin, and keeps every head within the stated bound throughout.

**Key facts.** `Complexity.P_subset_PSPACE`, `Complexity.b2b_clean_run`.
