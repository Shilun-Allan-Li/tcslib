<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/Reductions.lean :: Randomized.InBPP.of_randReducible -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Closure Under Randomized Reductions

**Claim.** If $B$ is randomized reducible to $C$ and $C$ belongs to the bounded-error class for the polynomial-time verifier model, then $B$ belongs to that class as well.

**Proof.** Let the reduction use $q=\mathrm{polyLen}(a_1,k_1,|x|)$ random bits. Its output, together with the reduction's correctness guarantee, identifies whether $x$ is in $B$ with probability at least $2/3$. First amplify the verifier for $C$ to success probability at least $23/24$ (`InBPP.inBPPAt_23_24`). The composite verifier uses the first $q$ random bits to form the reduction's output and the following bits to run this amplified verifier. It accepts or rejects according to the latter answer. Polynomial-time composition makes this verifier efficient (`polyTimeComputable_composeMap`), and the polynomial output-length bound for the reduction (`Complexity.PolyTimeComputable.output_length_le`) gives a polynomial bound on the total randomness required. The length estimate for the second-stage randomness (`polyLen_length_pairEncode_le`) supplies an explicit polynomial allowance large enough for that stage, while the chosen total bound accommodates both stages.

For either desired answer $b$, condition on the first-stage event that the reduction correctly identifies membership in $B$. Given any first-stage random string with this property, the amplified verifier returns $b$ with probability at least $23/24$; padding unused random bits does not change its distribution (`randProb_take`). The probability that both stages succeed is therefore at least $(2/3)(23/24)=23/36$, which exceeds $5/8$. The two-stage probability estimate is the random-bit concatenation bound (`randProb_append_ge`), and rewriting the composite verifier's random string into its first and second segments uses the probability-preserving equivalence (`randProb_congr`). This proves that the composite verifier has success at least $5/8$ for both membership and nonmembership. Majority amplification then upgrades this to the required $2/3$ guarantees (`InBPPAt.inBPP_of_5_8`).

**Key facts.** `Complexity.PolyTimeComputable.output_length_le`, `Randomized.InBPP.inBPPAt_23_24`, `Randomized.polyTimeComputable_composeMap`, `Randomized.polyLen_length_pairEncode_le`, `Randomized.randProb_take`, `Randomized.randProb_append_ge`, `Randomized.randProb_congr`, `Randomized.InBPPAt.inBPP_of_5_8`.
