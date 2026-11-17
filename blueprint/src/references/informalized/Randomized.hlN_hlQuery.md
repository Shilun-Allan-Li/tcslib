<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/BiasedCoinHalting.lean :: Randomized.hlN_hlQuery -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Query String Parameters

**Claim.** For all natural numbers $N,j$, the query string of $N$ ones, then a zero, then $4^{j+1}$ ones has head-output length $N$ and rest-output logarithmic parameter $j+1$.

**Proof.** Write the query string as the encoding of $N$ followed by a suffix of $4^{j+1}$ ones. The head-transducer encoding property says that its output is exactly $N$ ones, so its length is $N$ (`Complexity.BinArith.uHead_encodeNat`). The corresponding rest-transducer property says that its output is precisely the appended suffix (`Complexity.BinArith.uRest_encodeNat`), whose length is $4^{j+1}$. Taking the base-$4$ natural logarithm of that length gives $j+1$, as required.

**Key facts.** `Complexity.BinArith.uHead_encodeNat`, `Complexity.BinArith.uRest_encodeNat`.
