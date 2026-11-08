<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Constructions/PairwiseIndependence.lean :: FABL.n_le_two_pow_pairwiseIndependentRowCount_sub_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Row-Count Parameter Bound

**Claim.** For $m=\max\{1,\lceil\log_2(n+1)\rceil\}$, one has $n\le 2^m-1$.

**Proof.** The defining property of the ceiling logarithm gives $n+1\le 2^{\lceil\log_2(n+1)\rceil}$. Since $m$ is at least this ceiling, and exponentiation with base $2$ is increasing, $2^{\lceil\log_2(n+1)\rceil}\le 2^m$. Hence $n+1\le 2^m$, which is equivalent to $n\le 2^m-1$.
