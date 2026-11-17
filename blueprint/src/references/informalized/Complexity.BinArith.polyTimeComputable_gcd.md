<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/ClassP/BinaryArith/ModPow.lean :: Complexity.BinArith.polyTimeComputable_gcd -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: low -->

# Polynomial-Time Greatest Common Divisor

**Claim.** The function returning the binary representation of the greatest common divisor of the natural numbers decoded from a bit string is polynomial-time computable.

**Proof.** Initialize the computation by pairing the two decoded components. This initialization is polynomial-time computable. The invariant for this encoded state, $\mathrm{GcdInv}$, records the relationship between the original inputs and the current pair; it holds initially, and one greatest-common-divisor step preserves it. Each step is polynomial-time computable.

The iteration theorem gives polynomial-time computability of running the step for $2(|z|+1)$ iterations, once the intermediate states are shown to have polynomially bounded length. Invariant preservation identifies each intermediate state as an encoding of two numbers whose bit-string lengths are bounded by those of the initial decoded components; the pair-encoding length formula then gives the required bound.

To identify the final value, use the invariant and a decreasing measure. While the measure is positive, each step strictly decreases it; when it is zero, the step fixes the state. The initial measure is at most $2(|z|+1)$: its size term is controlled by bounding the product of the represented numbers below the power of two determined by the total lengths of the decoded components, and those lengths together are bounded by $|z|$. Therefore after the chosen number of iterations the measure is zero. At that point the product of the represented numbers has size zero, so the product itself is zero. The invariant and the measure's terminal condition force the second represented number to be zero. The invariant also identifies the first represented number with the gcd of the original inputs. Finally, project the first component of the iterated state and normalize its bit representation; projection, normalization, and composition preserve polynomial-time computability, yielding the required binary gcd.

**Key facts.** `Complexity.polyTimeComputable_pairFstD`, `Complexity.polyTimeComputable_pairSndD`, `Complexity.PolyTimeComputable.pairEncode`, `Complexity.BinArith.iterate_invariant`, `Complexity.BinArith.gcdInv_step`, `Complexity.BinArith.polyTimeComputable_iterate`, `Complexity.length_pairEncode`, `Complexity.BinArith.polyTimeComputable_gcdStep`, `Complexity.BinArith.iterate_measure_eq_zero`, `Complexity.length_pairFstD_le`, `Complexity.length_pairSndD_le`, `Complexity.length_pair_components_le`, `Complexity.BinArith.pairFstD_pairEncode`, `Complexity.BinArith.pairSndD_pairEncode`, `Complexity.LogProg.bitsVal_lt_two_pow`, `Complexity.PolyTimeComputable.comp`, `Complexity.BinArith.polyTimeComputable_normBits`.

**Caveat.** The invariant GcdInv and measure gcdMeasure are not defined in the supplied payload, so their precise mathematical content and the final identification of the first component with the gcd cannot be fully spelled out from the provided statements.
