<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/TuringMachine/Build/Catalog.lean :: Turing.FinTM.computesFunInTime_pairConcat_spaceUsed -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Pair Concatenation with a Space Bound

**Claim.** A finite Turing machine outputs the concatenated parsed pair components, or the empty word when parsing fails, in linear time and uses at most a constant multiple of the input length plus one work-tape cells at every time.

**Proof.** Take `f2_pairExtractTM` with both selection flags true and set $c=6$. Its computation theorem `f2_pairExtract_computes` gives the desired output in $5(|x|+1)$ steps; the time monotonicity property `ComputesInTime.mono` extends this to $6(|x|+1)$. Splitting on the parser result identifies the machine's output with the stated function. For space, the general estimate `f2_space_of_time` bounds usage at any time by the number of work tapes times the time bound plus one. Here there is one work tape and the established run length is $5(|x|+1)$, so usage is at most $5(|x|+1)+1\le 6(|x|+1)$.

**Key facts.** `Turing.FinTM.f2_pairExtract_computes`, `Turing.FinTM.ComputesInTime.mono`, `Turing.FinTM.f2_space_of_time`.
