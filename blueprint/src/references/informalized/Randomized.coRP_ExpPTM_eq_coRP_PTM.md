<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/RPExpected.lean :: Randomized.coRP_ExpPTM_eq_coRP_PTM -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Equality of coRP Classes

**Claim.** The class of complements of languages in RP with expected polynomial time equals the class of complements of languages in RP with polynomial worst-case time.

**Proof.** For any language $L$, membership of $L$ in the first coRP class means exactly that $L^c$ belongs to the expected-polynomial-time RP class, while membership in the second means that $L^c$ belongs to the polynomial worst-case-time RP class. The theorem identifying these two RP classes therefore makes these membership conditions equivalent (RP_ExpPTM_eq_RP_PTM). Since this holds for every $L$, the coRP classes are equal.

**Key facts.** `Randomized.RP_ExpPTM_eq_RP_PTM`.
