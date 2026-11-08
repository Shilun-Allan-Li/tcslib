<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/CoalitionalInfluenceAsymptotics.lean :: FABL.eventually_coalitionalInfluenceToward_criticalTribes_one_le_log_bound -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Critical tribes coalitional influence bound

**Claim.** For all sufficiently large $w$, every coalition $J$ of size at most $k$ has influence toward $1$ at most $2k\log d/d$, where $d$ is the critical tribes dimension.

**Proof.** Choose $w$ sufficiently large that $w\ge1$ and the bound $2^{-w}\le 2\log d/d$ holds. For any $k$ and coalition $J$ with $|J|\le k$, the critical tribes coalition estimate gives influence toward $1$ at most $k2^{-w}$ ($\texttt{coalitionalInfluenceToward\_criticalTribes\_one\_le$). Since $k\ge0$, multiplying the eventual estimate for $2^{-w}$ by $k$ preserves its direction and yields $k2^{-w}\le 2k\log d/d$.

**Key facts.** `FABL.coalitionalInfluenceToward_criticalTribes_one_le`, `FABL.eventually_inv_two_pow_le_two_mul_log_dimension_div_dimension`.
