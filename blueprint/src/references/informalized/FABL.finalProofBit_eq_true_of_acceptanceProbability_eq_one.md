<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/TestingAmplification.lean :: FABL.finalProofBit_eq_true_of_acceptanceProbability_eq_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Perfect Acceptance Forces the Final Proof Bit

**Claim.** If the odd-weight partial-sum PCPP system accepts $(w,p)$ with probability $1$, then the last bit of $p$ is true.

**Proof.** 1. Probability-one acceptance implies acceptance at every seed in the support of the seed distribution, by the equivalence between acceptance probability one and acceptance on the support (`acceptanceProbability_eq_one_iff_support_amplification`). The seed that selects the final-bit check belongs to the support: the seed distribution is uniform, so each seed has nonzero mass.
2. At this seed, the verifier queries the last proof bit, and its acceptance rule accepts exactly when that bit is true. The support conclusion therefore gives that the image of the last proof bit under the Boolean-to-$\mathbb{F}_2$ equivalence is $1$.
3. Since that equivalence is injective and sends `true` to $1$, the last proof bit itself is true.

**Key facts.** `FABL.acceptanceProbability_eq_one_iff_support_amplification`.
