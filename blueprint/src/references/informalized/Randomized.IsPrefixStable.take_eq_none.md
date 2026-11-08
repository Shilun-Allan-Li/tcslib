<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/ExpectedTime.lean :: Randomized.IsPrefixStable.take_eq_none -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Nonhalting Passes to Prefixes

**Claim.** If a prefix-stable procedure returns no value on $w$, then it returns no value on every prefix of $w$.

**Proof.** Consider the result of the procedure on the specified prefix. If it is already no value, the claim follows. Otherwise it equals some value $a$. By the fact that halting on a prefix determines the output on the full run (\texttt{IsPrefixStable.of\_take}), the procedure must return $a$ on $w$ as well. That contradicts the assumption that it returns no value on $w$.

**Key facts.** `Randomized.IsPrefixStable.of_take`.
