<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Primitives.lean :: Turing.FinTM.emitterSplit_result -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Equality of Split Search Outputs

**Claim.** Encoding the split at the length of the first accepted split-step iterate gives the same word as encoding the split at the index returned by the least-index search for $i+f(i)=|w|$; if the search returns none, both outputs are empty.

**Proof.** The orbit-search lemma identifies the first accepted iterate index with the result of the least-index search. If that search returns none, both displayed outputs are empty by their definitions. If it returns an index $i$, then $i\le |w|$, and the orbit formula says the $i$th iterate is a word of length $i$. Thus the two pieces taken from $w$ have exactly the same split index on both sides, so their encodings agree.

**Key facts.** `Turing.FinTM.emitterSplit_find`, `Turing.FinTM.splitStep_orbit`.
