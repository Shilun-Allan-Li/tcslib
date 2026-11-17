<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/MajorityFourierTailAsymptotics.lean :: FABL.limitingMajorityFourierWeightAbove_eq_shifted_tsum -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourier weight tail as a shifted sum

**Claim.** For every $k$, the limiting majority Fourier weight above $k$ equals $\sum_{r=0}^{\infty} w_{k+1+r}$, where $w_j$ is the limiting majority Fourier weight at level $j$.

**Proof.** The indices in the tail are precisely the natural numbers $j$ satisfying $k<j$. They are enumerated bijectively by $r\mapsto k+1+r$: each such index has a unique offset $r$ from $k+1$. Reindexing the sum over the tail by this bijection gives the stated shifted infinite sum.
