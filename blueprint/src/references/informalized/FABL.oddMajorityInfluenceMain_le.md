<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter02/TotalInfluence/MajorityInfluence.lean :: FABL.oddMajorityInfluenceMain_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Lower Bound for Majority Influence

**Claim.** For every natural number $m$, $\sqrt{2/(\pi(2m+1))}$ is at most $\binom{2m}{m}/2^{2m}$.

**Proof.** Both quantities are nonnegative, so it suffices to compare their squares. The square of the main term is $2/(\pi(2m+1))$ by `oddMajorityInfluenceMain_sq`. The identity `oddMajorityInfluence_sq_mul_wallis` expresses the squared influence as $1/((2m+1)W_m)$, where $W_m$ is the Wallis term. Wallis's lower bound $W_m\le \pi/2$ then gives $1/((2m+1)W_m)\ge 2/(\pi(2m+1))$. Comparing squares and using nonnegativity proves the result.

**Key facts.** `FABL.oddMajorityInfluenceMain_sq`, `FABL.oddMajorityInfluence_pos`, `FABL.oddMajorityInfluence_sq_mul_wallis`.
