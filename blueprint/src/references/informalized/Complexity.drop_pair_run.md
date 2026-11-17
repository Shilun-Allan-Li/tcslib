<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Logspace/QueryReshape.lean :: Complexity.drop_pair_run -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Pair-Scan Run

**Claim.** Under the register bound, stride-aligned limit, and bit-reading hypotheses, the scan either reaches a false-answer state after advancing by a stride multiple no greater than the length of $w$, or, when $w$ decodes as a pair with first component $a$, reaches the scan-complete state with pointer advanced by $s_\ell(2|a|+2)$. The computation invariant holds throughout the run.

**Proof.** The machine's scan states compare the pointer with the prescribed limit, read the encoded pair through the oracle, and advance the pointer in increments of the layer's stride. The general aligned-pair loop theorem (`Complexity.LogProg.alignedPair_loop`) applies with pointer register $0$, limit register $s_\ell$, stride $s_\ell$, and the scan, first-bit, second-bit, and read states for the chosen layer. Its required distinctness of pointer and limit follows from the layer-specific register indices, and the state-transition obligations follow directly from the definition of the scan machine and its advance function. The given register bound and limit equation supply the loop's numerical hypotheses. At each read, the oracle answer agrees with the corresponding bit of $w$: `drop_bit` identifies the oracle query with the bit of the encoded input at the stride-aligned position, and the assumed alignment hypothesis identifies that bit with the bit of $w$. The loop theorem therefore yields the stated failure or successful-parse endpoint, along with the invariant at each preceding configuration.

**Key facts.** `Complexity.LogProg.alignedPair_loop`, `Complexity.drop_bit`.
