<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Util/List.lean :: List.count_take_succ_getD -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Counting a Longer Prefix with Default Lookup

**Claim.** For a finite list $l$, elements $x,d$, and $i<\operatorname{length}(l)$, the number of occurrences of $x$ among the first $i+1$ entries is its count among the first $i$ entries, plus one exactly when the entry at position $i$, read with default $d$, equals $x$.

**Proof.** By the preceding prefix-count identity (`List.count_take_succ`), the count in the longer prefix is the count in the shorter prefix plus one exactly when $l[i]=x$. Since $i$ is in range, lookup with default $d$ returns the actual entry $l[i]$ (`List.getD_eq_getElem`). Substituting this equal value into the condition proves the formula.

**Key facts.** `List.count_take_succ`.
