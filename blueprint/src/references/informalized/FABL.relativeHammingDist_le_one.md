<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/FKN.lean :: FABL.relativeHammingDist_le_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Upper Bound on Relative Hamming Distance

**Claim.** For a finite nonempty set $\Omega$, a set $\beta$ with decidable equality, and functions $f,g:\Omega\to\beta$, their relative Hamming distance is at most $1$.

**Proof.** The Hamming distance counts a subset of the inputs, so it is at most the total number of inputs in $\Omega$. Since $\Omega$ is nonempty, its cardinality is positive. Dividing the Hamming bound by this positive cardinality gives a relative distance at most $1$.
