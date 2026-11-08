<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_splitLoop_result -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Agreement of split procedures

**Claim.** The result obtained from the split procedure’s first accepted index, encoding the corresponding prefix and suffix, agrees with the result obtained from the polynomial search: it encodes the prefix and suffix at a solution index, or is empty if there is no solution.

**Proof.** First replace the split procedure’s search by the polynomial search using the equivalence of their first successful indices (`f2_splitFind_eq`). If the polynomial search returns no index, both sides are empty. If it returns $i$, that index belongs to the search range, so $i\le |w|$. The split-step orbit identity (`f2_splitStep_orbit`) identifies the counter after $i$ iterations with a word of $i$ true bits, whose length is $i$. Thus both procedures take the prefix of $w$ of length $i$ and the suffix remaining after that prefix, and their encodings agree.

**Key facts.** `Turing.FinTM.f2_splitFind_eq`, `Turing.FinTM.f2_splitStep_orbit`.
