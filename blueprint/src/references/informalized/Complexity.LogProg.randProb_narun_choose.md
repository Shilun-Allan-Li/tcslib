<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/NARMProb.lean :: Complexity.LogProg.randProb_narun_choose -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Choice Splits Run Probability

**Claim.** At a binary choice state, the probability of a configuration property after $N+1$ random choice bits is the average of its probabilities after $N$ bits from the two successor states.

**Proof.** Partition the length-$(N+1)$ choice words according to their first bit. If that bit is true, the machine takes the branch to $l_1$; if it is false, it takes the branch to $l_0$. In either case, the remaining $N$ bits run from the corresponding successor configuration, by the one-step run equation and the transition rule for a choice instruction (`narun_cons`, `nastep_choose`). Hence the two conditional probabilities are precisely the length-$N$ probabilities from those successors (`randProb_congr`). The probability of the original event is the average of these two conditional probabilities, by the one-bit decomposition of uniform random choice words (`randProb_succ`).

**Key facts.** `Complexity.LogProg.narun_cons`, `Complexity.LogProg.nastep_choose`, `Randomized.randProb_congr`, `Randomized.randProb_succ`.
