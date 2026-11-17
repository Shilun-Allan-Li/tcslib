<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Primitives.lean :: Turing.FinTM.emitterSplit_find -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Orbit Search and Split Search

**Claim.** Searching the indices from $0$ through $|w|$ for the first iterate of the split step satisfying the acceptance test returns the same result as searching for the least $i$ with $i+f(i)=|w|$; both return none if there is no such index.

**Proof.** The two searches use the same finite list of candidate indices, so it suffices to check that their Boolean tests agree at each candidate. For any index $i$ in the list, we have $i\le |w|$. The split-step orbit formula says that the $i$th iterate from the empty word is the word consisting of $i$ true bits, and hence has length $i$. The acceptance test on this iterate is therefore exactly the assertion $i+f(i)=|w|$. Since the tests agree at every candidate, the first successful index—and the result when none succeeds—are the same.

**Key facts.** `Turing.FinTM.catalogFind_congr`, `Turing.FinTM.splitStep_orbit`.
