<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.f2_splitStep_inv -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Length Bound for a Split Step

**Claim.** If $|s|\le |w|+1$, then the split step determined by $w$ produces a word of length at most $|w|+1$.

**Proof.** If $|s|\le |w|$, the step appends one symbol, so the new length is $|s|+1\le |w|+1$. Otherwise the step leaves $s$ unchanged; the hypothesis $|s|\le |w|+1$ already gives the required bound.
