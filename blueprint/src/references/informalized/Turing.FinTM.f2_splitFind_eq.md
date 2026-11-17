<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_splitFind_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Split search equals polynomial search

**Claim.** Searching indices from $0$ through the word length for the first successful split acceptance test gives the same optional index as searching that range for a solution of $i+C(i+1)^e=|w|$.

**Proof.** Compare the two Boolean predicates at every index in the search range. The orbit identity for the split step (`f2_splitStep_orbit`) says that after $i$ iterations from the empty word, the counter is a word of $i$ true bits, hence has length $i$. Substituting this length into the acceptance test shows that it is true exactly when $i+C(i+1)^e=|w|$, which is the polynomial search predicate. Since the predicates agree on every element of the range, their first successful elements, including the possibility that neither has one, agree (`f2_catalogFind_congr`).

**Key facts.** `Turing.FinTM.f2_splitStep_orbit`, `Turing.FinTM.f2_catalogFind_congr`.
