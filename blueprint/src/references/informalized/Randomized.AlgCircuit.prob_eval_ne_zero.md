<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/Fingerprint.lean :: Randomized.AlgCircuit.prob_eval_ne_zero -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Schwartz–Zippel Detection Probability

**Claim.** For a circuit whose associated polynomial is nonzero, a uniformly sampled Boolean string, interpreted through the prescribed blocks and shifted by one, gives a nonzero circuit evaluation with probability at least $15/16$.

**Proof.** Put $b=|C|+4$ and let $S$ be the integer interval from $1$ through $2^b$, which has cardinality $2^b$. The associated polynomial has total degree at most $2^{|C|}$ (`Randomized.AlgCircuit.totalDegree_toMvPolynomial_le`). Since it is nonzero, the Schwartz–Zippel bound on the product set $S^n$ says that the fraction of inputs where it evaluates nonzero is at least $1-2^{|C|}/2^b=15/16$ (`Randomized.schwartz_zippel`). The map sending each coordinate $a$ in $	ext{Fin}(2^b)$ to $a+1$ is a bijection onto $S$, so it preserves this fraction; circuit evaluation agrees with evaluation of its associated polynomial (`Randomized.AlgCircuit.eval_toMvPolynomial`). Finally, blocks of $b$ Boolean bits are uniformly distributed over $	ext{Fin}(2^b)^n$, and their shifted values are exactly these inputs (`Randomized.randProb_blocks`). Hence the probability over Boolean strings has the same lower bound.

**Key facts.** `Randomized.AlgCircuit.totalDegree_toMvPolynomial_le`, `Randomized.schwartz_zippel`, `Randomized.AlgCircuit.eval_toMvPolynomial`, `Randomized.randProb_blocks`.
