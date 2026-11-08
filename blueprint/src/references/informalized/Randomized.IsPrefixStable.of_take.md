<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/ExpectedTime.lean :: Randomized.IsPrefixStable.of_take -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Halting on a Prefix Determines the Run

**Claim.** If a prefix-stable procedure returns $a$ on the length-$t$ prefix of $w$, then it returns $a$ on all of $w$.

**Proof.** Write $w$ as the concatenation of its length-$t$ prefix and the remaining suffix: $w=\operatorname{take}_t(w)\mathbin{++}\operatorname{drop}_t(w)$. Prefix stability says that extending a string on which the procedure returns $a$ preserves that output. Apply this to the prefix and its remaining suffix to conclude that the procedure returns $a$ on $w$.
