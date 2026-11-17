<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/FKN.lean :: FABL.fkn_family_isBigO -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Asymptotic FKN Bound

**Claim.** For a family of Boolean functions whose first-level Fourier weight is at least $1-\delta$, with $\delta$ nonnegative and at most $1/1600$, one can choose for each function a signed coordinate whose relative Hamming distance is at most $1601\delta$. Consequently, these distances are $O(\delta)$ along the given filter.

**Proof.** For each index, apply the FKN theorem to the function and its parameter $\delta$. Its hypotheses are exactly the assumed nonnegativity, upper bound, and first-level weight condition. It supplies a coordinate and sign with relative Hamming distance at most $1601\delta$. Choose one such pair at every index. Relative Hamming distance is nonnegative, as is $\delta$, so the norms of the resulting distance and parameter are just their values. The pointwise bound with constant $1601$ is precisely the criterion for the distance family to be $O(\delta)$ along the filter.

**Key facts.** `FABL.fkn`, `FABL.relativeHammingDist_nonneg`.
