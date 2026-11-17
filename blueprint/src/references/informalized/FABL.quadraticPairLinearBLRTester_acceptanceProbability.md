<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/QuadraticPCPP.lean :: FABL.quadraticPairLinearBLRTester_acceptanceProbability -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Quadratic-pair linear BLR probability

**Claim.** For every $n$, the quadratic-pair linear tester's acceptance probability on the oracle determined by $\ell$ and $q$ equals the three-query BLR tester's acceptance probability on $\ell$; both test whether $\ell(x)+\ell(y)=\ell(x+y)$ for independent uniform $x,y\in\mathbb{F}_2^n$.

**Proof.** Both testers sample the same uniform seed pair $(x,y)$. The quadratic-pair tester queries the oracle at the linear addresses for $x$, $y$, and $x+y$, and has a fourth unused query. On these three addresses the oracle returns $\ell(x)$, $\ell(y)$, and $\ell(x+y)$; the tester accepts exactly when the first two values sum to the third. This is the BLR tester's acceptance condition on the same seed pair. Therefore their acceptance indicators agree for every seed, and averaging over the common uniform distribution gives equal acceptance probabilities. The matrix oracle $q$ is never queried.
