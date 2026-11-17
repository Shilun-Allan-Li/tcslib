<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/Primality.lean :: Randomized.compositeTest_pairEncode -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Composite Test on Encoded Inputs

**Claim.** For any Boolean strings $x$ and $r$, the composite test on the encoding of $(x,r)$ equals the composite verifier applied to $x$ and $r$.

**Proof.** First, the pair encoding lets the two prefix operations in the test recover respectively the first $|x|+3$ bits of $r$ and the first $|x|+3$ bits after that prefix. The decoded first component of the input is $x$, and its padded version is $x$ followed by three true bits. The binary value of the encoding of $x$ is therefore $\operatorname{bitsVal}(x)$: the value of $\operatorname{Nat.bits}(n)$ is $n$ (Complexity.LogProg.bitsVal_bits), and decoding a pair encoding recovers its components (Complexity.pairFstD_pairEncode and Complexity.pairSndD_pairEncode).

The test’s comparisons with $2$ consequently become the verifier’s comparisons with $2$. Its parity check also agrees with the verifier’s: the value modulo $2$ is the Boolean value of the first bit (Complexity.BinArith.bitsVal_mod_two). Thus the two procedures take matching branches when the value is below $2$, equals $2$, or is even. In the remaining case the value is odd and greater than $2$. On this branch, the test’s two calls to the liar-round predicate reduce, by the characterization of that predicate on encoded inputs (Randomized.liarRound_pairEncode), to the two Euler-liar checks on the corresponding sampled prefixes. Together these are exactly the two rounds in the composite verifier, proving the equality.

**Key facts.** `Complexity.pairFstD_pairEncode`, `Complexity.pairSndD_pairEncode`, `Complexity.LogProg.bitsVal_bits`, `Complexity.BinArith.bitsVal_mod_two`, `Randomized.liarRound_pairEncode`.
