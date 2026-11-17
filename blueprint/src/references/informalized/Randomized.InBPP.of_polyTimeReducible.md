<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/Inclusions.lean :: Randomized.InBPP.of_polyTimeReducible -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Closure Under Polynomial-Time Reductions

**Claim.** If $L'$ is polynomial-time many-one reducible to $L$, and $L$ belongs to the bounded-error class for the polynomial-time verifier model, then $L'$ also belongs to that class.

**Proof.** Let $f$ be the reduction, so $x\in L'$ exactly when $f(x)\in L$. Take an efficient verifier $M$ for $L$ with randomness bound $\mathrm{polyLen}(a,k,|y|)$. The verifier for $L'$ computes $f(x)$ and runs $M$ on that output, using the initial part of its random string for $M$. Polynomial-time closure provides constants $a',k'$ making this composite verifier efficient and ensuring that its random-string bound is at least the number of bits needed by $M$ on $f(x)$ (`exists_eff_reducedVerifier`). For every input $x$, the reduction's output length bound ensures that this latter number of bits fits within the allotted bound. The initial segment has exactly the distribution of the required shorter random string, so the acceptance and rejection probabilities are preserved (`randProb_take`). The correctness equivalence for the reduction transfers both membership and nonmembership guarantees from $L$ to $L'$.

**Key facts.** `Randomized.exists_eff_reducedVerifier`, `Randomized.randProb_take`.
