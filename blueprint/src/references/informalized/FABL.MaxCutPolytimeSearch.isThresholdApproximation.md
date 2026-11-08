<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/CSPAlgorithms.lean :: FABL.MaxCutPolytimeSearch.isThresholdApproximation -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Threshold guarantee for an optimal assignment

**Claim.** The encoded Max-Cut search algorithm is a $(1,1)$-threshold approximation: on every encoded instance with optimum at least $1$, it returns a feasible assignment of value at least $1$.

**Proof.** Take any valid encoded input and decode it as an instance $P$. The encoding law for successful decoding shows that the input is the canonical encoding of $P$, so the search algorithm’s specified behavior makes its output the encoding of the optimal assignment. Decoding the canonical instance and assignment encodings shows that this output is feasible. If the optimum is at least $1$, the fact that every optimum is at most $1$ forces the optimum to equal $1$, so $P$ is satisfiable. The chosen maximum-cut assignment fully satisfies every constraint in a satisfiable instance. By the characterization of value $1$ as full satisfaction, its value is $1$, establishing the threshold guarantee.

**Key facts.** `FABL.CSPInstance.optimum_le_one`, `FABL.maxCutSatisfyingAssignment_fullySatisfied`, `FABL.CSPInstance.value_eq_one_iff_fullySatisfied`.

**Caveat.** The supplied Lean theorem proves the exact $(1,1)$ guarantee for the specified optimal-assignment search structure; it does not formalize the stated Goemans–Williamson approximation claim.
