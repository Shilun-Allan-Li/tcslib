<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_splitFind_none -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# No split solution and failed tests

**Claim.** There is no index in the specified range solving $i+C(i+1)^e=|w|$ exactly when every split acceptance test for indices $i\le |w|$ fails.

**Proof.** Use the equivalence between iterated split search and polynomial search (`f2_splitFind_eq`) to replace the equation’s search result by the search whose predicate is the split acceptance test. A search over a finite list returns no element exactly when its predicate is false at every element of that list. The list of indices from $0$ through $|w|$ contains exactly the natural numbers $i\le |w|$, so this condition is precisely that all the stated acceptance tests are false.

**Key facts.** `Turing.FinTM.f2_splitFind_eq`.
