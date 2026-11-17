<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/ThresholdFunctions/Polynomial.lean :: BooleanAnalysis.ThresholdFunctions.MultilinearPolynomial.eval_of_degree_le_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation of a degree-one polynomial

**Claim.** A polynomial whose coefficients vanish on sets of size greater than one evaluates as its constant coefficient plus the sum of its singleton coefficients times the corresponding coordinate signs.

**Proof.** In the finite sum defining the evaluation, retain only the empty set and singleton sets. Every other set has cardinality greater than one, so its coefficient vanishes by the degree assumption. The empty-set character is the empty product, hence equals one. The singleton character for $\{i\}$ is the sign of coordinate $i$. Reindexing the singleton terms by $i\in[n]$ gives the stated formula.
