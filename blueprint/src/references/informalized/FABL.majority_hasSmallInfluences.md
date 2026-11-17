<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Pseudorandomness/Examples.lean :: FABL.majority_hasSmallInfluences -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Small Influences of Majority

**Claim.** For every natural number $n$, majority on $n$ signs has each coordinate influence at most $1/\sqrt n$, and hence has small influences at that bound.

**Proof.** By the characterization of small influences as a coordinatewise bound on the ordinary influence (\texttt{hasSmallInfluences_iff}), it suffices to bound the influence at each coordinate $i$. Majority is transitive symmetric and monotone, as supplied by \texttt{majority_transitiveSymmetric} and \texttt{majority_monotone}. The general influence bound for a transitive symmetric monotone Boolean function (\texttt{influence_le_one_div_sqrt_of_transitiveSymmetric_monotone}) then gives $\operatorname{Inf}_i[\operatorname{Maj}_n]\le 1/\sqrt n$ for every $i$, proving the claim.

**Key facts.** `FABL.hasSmallInfluences_iff`, `FABL.majority_transitiveSymmetric`, `FABL.majority_monotone`, `FABL.influence_le_one_div_sqrt_of_transitiveSymmetric_monotone`.
