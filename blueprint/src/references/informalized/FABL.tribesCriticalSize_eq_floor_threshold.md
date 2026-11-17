<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter04/Tribes.lean :: FABL.tribesCriticalSize_eq_floor_threshold -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Critical Size as a Threshold Floor

**Claim.** For every positive integer $w$, the critical size of tribes of width $w$ is the greatest integer not exceeding the logarithmic threshold $\log 2/(-\log(1-2^{-w}))$.

**Proof.** Let $k$ be the greatest integer not exceeding the threshold. The threshold is nonnegative (`criticalThreshold_nonneg`), so $k$ is at most the threshold. By the equivalence between being a candidate and lying below the threshold (`candidate_iff_cast_le_threshold`), $k$ is a candidate. Also, the threshold is at most $2^w$ (`criticalThreshold_le_two_pow`), hence at most the search bound $2^{w+2}$; therefore $k$ lies within the range used to define the greatest candidate. Conversely, the critical size itself is a candidate (`tribesCriticalSize_spec`), so the same equivalence shows it is at most the threshold, and thus at most its floor. Since $k$ is an in-range candidate, the greatest-candidate property makes the critical size at least $k$. The two inequalities prove equality.

**Key facts.** `FABL.criticalThreshold_nonneg`, `FABL.candidate_iff_cast_le_threshold`, `FABL.criticalThreshold_le_two_pow`, `FABL.tribesCriticalSize_spec`.
