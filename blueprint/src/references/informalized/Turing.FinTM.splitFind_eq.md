<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Primitives.lean :: Turing.FinTM.splitFind_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Orbit search equals arithmetic search

**Claim.** For every $C,e$ and Boolean word $w$, searching the indices from $0$ through $|w|$ for the first iterate of the split step satisfying the acceptance test gives the same result as the arithmetic search for the least index $i$ with $i+C(i+1)^e=|w|$, including failure when no such index exists.

**Proof.** On the finite list of candidate indices, replace the orbit-based acceptance test by the arithmetic test; the first-search invariance lemma applies once the predicates are shown to agree at every candidate. For an index $i\le |w|$, the split-step orbit is the word of $i$ copies of $1$. Its length is therefore $i$, so the acceptance condition becomes exactly $i+C(i+1)^e=|w|$. Thus the two predicates agree throughout the search list, and their first successful indices—or their failure to find one—coincide.

**Key facts.** `Turing.FinTM.catalogFind_congr`, `Turing.FinTM.splitStep_orbit`.
