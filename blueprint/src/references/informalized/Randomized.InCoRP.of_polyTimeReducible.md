<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/Inclusions.lean :: Randomized.InCoRP.of_polyTimeReducible -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# CoRP closure under polynomial-time reductions

**Claim.** If $L'$ is polynomial-time many-one reducible to $L$ and $L$ is in coRP for the polynomial-time verifier model, then $L'$ is also in coRP for that model.

**Proof.** Choose a polynomial-time reduction $f$ from $L'$ to $L$, so $x\in L'$ exactly when $f(x)\in L$. The complement equivalence follows: $x\notin L'$ exactly when $f(x)\notin L$. Thus the same function reduces the complement of $L'$ to the complement of $L$. By definition, the coRP assumption says that the complement of $L$ is in RP. Closure of RP under polynomial-time reductions (Randomized.InRP.of_polyTimeReducible) therefore puts the complement of $L'$ in RP, which is the assertion that $L'$ is in coRP.

**Key facts.** `Randomized.InRP.of_polyTimeReducible`.
