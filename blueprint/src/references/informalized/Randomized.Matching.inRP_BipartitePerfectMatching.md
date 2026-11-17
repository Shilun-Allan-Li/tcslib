<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/Matching.lean :: Randomized.Matching.inRP_BipartitePerfectMatching -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: low -->

# Bipartite Matching Is in RP

**Claim.** The language of encodings of bipartite graphs that have a perfect matching belongs to RP under the given verifier model, with the stated acceptance probability on members and certain rejection on nonmembers.

**Proof.** 1. Use the established efficient verifier for the Lovász determinant test, and first obtain its weak one-sided-error RP guarantee. Polynomial-time verifiers are closed under the amplification operation needed to convert that weak guarantee into the stated RP definition (Randomized.polyTimeModel_closedUnderAny and Randomized.inRPWeak_iff_inRP). The verifier's random-bit bound is cubic in the input length plus one.

2. Consider an input encoding a matrix $A$ with a perfect matching. Its length is $2n+n^2+2$: the pair encoding duplicates each of the $n$ unary marker bits, adds a two-bit delimiter, and appends the $n^2$ adjacency bits (Turing.length_pairEncode and Randomized.Matching.length_adjWord). Write $M=n^2+2n+3$, so $n^2$, the number of bits required per entry, and $1$ are each at most $M$. Also the input length plus one equals $M$. Thus the required $n^2\,\mathrm{lovaszBits}(n)$ random bits fit within the verifier's cubic bound. Here the bound $\mathrm{lovaszBits}(n)\le n+1$ is supplied by Randomized.Matching.lovaszBits_le.

3. The prime used as the coefficient field is indeed prime (Complexity.BinArith.lovaszPrime_prime). The bounds $2n\le 2^{\mathrm{lovaszBits}(n)}$ and $2^{\mathrm{clog}_2(2n)}<\mathrm{lovaszPrime}(n)$ ensure that the sample range is large enough and embeds into that field (Complexity.BinArith.two_mul_le_two_pow_lovaszBits and Complexity.BinArith.two_pow_lt_lovaszPrime). The verifier's acceptance event, on a well-formed encoding and with enough random bits, is exactly that the sampled Lovász matrix has nonzero determinant (Randomized.Matching.matchingVerifier_encodeBPM). The determinant-test probability bound then gives acceptance probability at least $1/2$. The weak RP-to-RP conversion, with its chosen amplification parameter, yields the required $2/3$ guarantee.

4. If an input is outside the language, either it is not a valid encoding of the specified form, in which case the verifier rejects directly, or it encodes a matrix with no perfect matching. In the latter case the Lovász matrix always has zero determinant, by Randomized.Matching.det_lovaszMatrix_eq_zero, so the verifier rejects for every random string. This proves the one-sided soundness condition.

**Key facts.** `Randomized.inRPWeak_iff_inRP`, `Randomized.polyTimeModel_closedUnderAny`, `Randomized.Matching.lovaszBits_le`, `Turing.length_pairEncode`, `Randomized.Matching.length_adjWord`, `Complexity.BinArith.lovaszPrime_prime`, `Complexity.BinArith.two_mul_le_two_pow_lovaszBits`, `Complexity.BinArith.two_pow_lt_lovaszPrime`, `Randomized.Matching.lovasz_test_zmod`, `Randomized.Matching.matchingVerifier_encodeBPM`, `Randomized.Matching.det_lovaszMatrix_eq_zero`, `Randomized.Matching.eff_matchingVerifier`.

**Caveat.** The proof source invokes a weak-to-standard RP conversion with parameter 1; the supplied upstream statements do not specify its probability calculation. The account records the conversion route, but the precise amplification step is not derivable from the listed statements alone.
