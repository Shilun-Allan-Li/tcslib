<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/LargeFourierCoefficient.lean :: FABL.mem_lowDegreeSubsets -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Membership in low-degree subsets

**Claim.** A set $S$ belongs to the family of subsets of $J$ of size at most $k$ exactly when $S\subseteq J$ and $|S|\le k$.

**Proof.** The family is the union, for $j=0,\ldots,k$, of the families of $j$-element subsets of $J$. Membership therefore says that $S$ is a subset of $J$ and has cardinality equal to one of those values of $j$. The latter condition is equivalent to $|S|\le k$, giving the stated characterization.

**Caveat.** The supplied informal statement describes a different Fourier-weight and influence claim. The formal statement and proof source instead establish this membership characterization.
