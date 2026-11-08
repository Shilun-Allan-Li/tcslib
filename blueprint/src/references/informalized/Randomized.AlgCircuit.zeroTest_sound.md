<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/Fingerprint.lean :: Randomized.AlgCircuit.zeroTest_sound -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Soundness of the Zero Test

**Claim.** If an algebraic circuit has nonzero associated polynomial and $N$ is at least its test length, then a uniformly chosen $N$-bit string makes the zero test return false with probability at least $2/3$.

**Proof.** First, the test depends only on the initial segment of the random string whose length is the circuit's test length. The probability of failure on an $N$-bit string therefore equals its probability on a string of exactly that length (`randProb_take` and `randProb_congr`).

Write $M$ for the modulus parameter of the circuit size, and, for an input block $u$, let $y(u)$ be the integer obtained by evaluating the circuit at the test point specified by $u$. Since the associated polynomial is nonzero, the evaluation bound `prob_eval_ne_zero` gives probability at least $15/16$ that $y(u)\ne 0$. Also, `natAbs_eval_testPoint_le` bounds $|y(u)|$ by the stated exponential bound. For every such nonzero value, `prob_exists_not_dvd` says that with probability at least $3/4$ over the modulus blocks, at least one sampled modulus fails to divide $y(u)$; its size hypothesis holds because the modulus parameter is at least $12$.

Combining the input and modulus blocks with the conditional probability estimate `randProb_append_ge` gives a lower bound of $(15/16)(3/4)=45/64$ for the probability that some sampled modulus does not divide $y(u)$. This is at least $2/3$. Finally, evaluation commutes with reduction modulo each test modulus (`eval_natCast_zmod`), and an integer is zero modulo a positive modulus exactly when that modulus divides it. Hence failure of divisibility for some trial is exactly failure of the zero-test condition, proving the claimed probability bound.

**Key facts.** `Randomized.randProb_take`, `Randomized.randProb_congr`, `Randomized.AlgCircuit.natAbs_eval_testPoint_le`, `Randomized.AlgCircuit.prob_eval_ne_zero`, `Randomized.prob_exists_not_dvd`, `Randomized.randProb_append_ge`, `Randomized.AlgCircuit.eval_natCast_zmod`.
