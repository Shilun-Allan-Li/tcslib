<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/LowDegreeF₂PolynomialLearning.lean :: FABL.lowDegreeF₂Eval_injective -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Uniqueness of Low-Degree Coefficients

**Claim.** For every $n$ and $\ell\in\mathbb{N}$, the map from coefficient assignments on subsets of $[n]$ of size at most $\ell$ to their Boolean functions on $\mathbb{F}_2^n$ is injective.

**Proof.** Take two coefficient assignments whose evaluations agree at every Boolean input. Extend each assignment to all subsets by setting its coefficients to zero on subsets of size greater than $\ell$. The extension lemma identifies the full algebraic normal form evaluation of each extended assignment with its original low-degree evaluation ($\mathrm{anfEval\_extendLowDegreeF₂Coefficients}$). Thus the two full evaluations agree. Injectivity of algebraic normal form evaluation then gives equality of the extended coefficient functions ($\mathrm{anfEval\_injective}$). Restricting this equality to subsets of size at most $\ell$ recovers equality of the original assignments.

**Key facts.** `FABL.anfEval_extendLowDegreeF₂Coefficients`, `FABL.anfEval_injective`.
