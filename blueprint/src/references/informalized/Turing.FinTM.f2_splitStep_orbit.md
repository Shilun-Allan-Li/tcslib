<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_splitStep_orbit -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Orbit of the Split Step

**Claim.** For every Boolean word $w$ and every $i\le |w|+1$, iterating its split step $i$ times from the empty word gives the word of $i$ true symbols.

**Proof.** Proceed by induction on $i$. For $i=0$, no step is performed and both words are empty. For the successor case, the induction hypothesis identifies the current word with $i$ true symbols. Since $i\le |w|$, the split step appends one true symbol. The result is therefore the word of $i+1$ true symbols, as required.
