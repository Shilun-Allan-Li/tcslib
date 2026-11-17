<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/BiasedCoinHalting.lean :: Randomized.hlD_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Depth Parameter Bound

**Claim.** For every finite binary string $x$, if $j=\lfloor\log_4 |u|\rfloor$ for the specified rest-transducer output $u$, then $4^j\le |x|+1$.

**Proof.** The rest-transducer output has length at most $|x|$ (`Complexity.BinArith.length_uRest_le`). If that output is empty, its natural logarithm parameter is zero, so the depth is $4^0=1\le |x|+1$. If its length is positive, the defining property of the natural logarithm gives $4^{\log_4 |u|}\le |u|$. Combining this with the output-length bound yields $4^j\le |x|\le |x|+1$.

**Key facts.** `Complexity.BinArith.length_uRest_le`.
