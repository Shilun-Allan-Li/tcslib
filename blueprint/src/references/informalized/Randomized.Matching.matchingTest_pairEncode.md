<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/Matching.lean :: Randomized.Matching.matchingTest_pairEncode -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Matching Test on Encoded Inputs

**Claim.** For any bit strings $x$ and $r$, running the matching test on their pair encoding gives the same Boolean result as the matching verifier on $(x,r)$.

**Proof.** Write $n$ for the length of the first decoded component of $x$, $w$ for its second decoded component, and $k$ for the Lovász bit length at $n$. Pair encoding and decoding recover $x$ and $r$. The verifier's first checks in the encoded test therefore reduce to checking that $x$ is the canonical encoding of a graph of size $n$, and that $r$ has length at least $n^2k$. The pair-equality characterization (`eqW_pairEncode`) and the encoding criterion (`eq_encodeBPM_iff`) identify the first check with $x=\operatorname{encodeBPM}(n,\operatorname{adjOfWord}(n,w))$. The length formula for unary multiplication (`length_mulU`) gives the second check as $n^2k\le |r|$.

If either check fails, both Boolean expressions are false, so the outputs agree. Suppose both hold. The encoding criterion also gives $|w|=n^2$. The doubling-loop specification (`dblLoop_spec`) shows that the computed parameter has length $k$, and the multiplication length formula gives the next parameter length $nk$. The coin extraction is consequently the prefix of $r$ of length $n(nk)$.

The row-generation identity (`zipWithW_lovaszRowW`) now identifies the constructed rows with the rows of block values masked by the adjacency word. The fact that these rows have the expected square shape (`length_lovaszRows`) allows the determinant algorithm's matrix specification (`detModAlg_pairEncode`) to apply. The rows-to-matrix identity (`matOfRows_lovaszRows`) identifies that matrix with the masked sample matrix over the Lovász prime field. Since the required prefix length is at most $|r|$, truncating to it does not change any sampled block (`lovaszSample_take`). Finally, the prime-field property (`lovaszPrime_prime`) supplies the field hypothesis for the determinant algorithm, and the bit-value identity (`bitsVal_bits`) turns its output bits back into the determinant's residue. A residue in the prime field is zero exactly when its representative is zero, so the test's final nonzero check agrees with the verifier's determinant check. The three Boolean checks thus coincide.

**Key facts.** `Complexity.BinArith.eqW_pairEncode`, `Randomized.Matching.eq_encodeBPM_iff`, `Complexity.BinArith.length_mulU`, `Complexity.BinArith.dblLoop_spec`, `Randomized.Matching.zipWithW_lovaszRowW`, `Randomized.Matching.length_lovaszRows`, `Complexity.BinArith.detModAlg_pairEncode`, `Randomized.Matching.matOfRows_lovaszRows`, `Randomized.Matching.lovaszSample_take`, `Complexity.BinArith.lovaszPrime_prime`, `Complexity.LogProg.bitsVal_bits`.
