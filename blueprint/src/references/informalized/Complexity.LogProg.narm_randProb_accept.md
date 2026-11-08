<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Machines/NARMProb.lean :: Complexity.LogProg.narm_randProb_accept -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Acceptance Probability for True

**Claim.** The probability that a uniformly chosen length-$T$ choice string makes the compiled machine halt with output exactly the single bit $1$ equals the probability that a uniformly chosen length-$N$ choice string makes the register program return true.

**Proof.** Use the equality of compiled and program acceptance probabilities with $b=\mathrm{true}$. For every length-$T$ choice string, the compiled machine halts by hypothesis, so the condition that its output is $[\mathrm{true}]$ already implies the stated pair of conditions: it halts and its output is $[\mathrm{true}]$. Thus the length-$T$ event in this theorem agrees pointwise with the output event in the preceding equality, and their probabilities are equal by invariance of the uniform choice probability under pointwise equivalent predicates. The preceding equality then identifies this with the probability that the register program returns true.

**Key facts.** `Complexity.LogProg.narm_randProb`, `Randomized.randProb_congr`.
