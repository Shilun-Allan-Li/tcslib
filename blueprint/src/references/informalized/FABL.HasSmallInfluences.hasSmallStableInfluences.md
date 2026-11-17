<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/HastadThreeSat.lean :: FABL.HasSmallInfluences.hasSmallStableInfluences -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Small Influences Imply Stable Influences

**Claim.** If $0\le\epsilon\le1$ and every coordinate has influence at most $\epsilon$, then every coordinate has stable influence at correlation parameter $1-\epsilon$ at most $\epsilon$.

**Proof.** Fix a coordinate $i$. Since $0\le\epsilon\le1$, the parameter $1-\epsilon$ lies in $[0,1]$. Stable influence at any parameter in this interval is at most ordinary influence (`stableInfluence_le_influence`). At parameter $1$, stable influence equals ordinary influence (`stableInfluence_one_eq_influence`); the hypothesis that the influences are at most $\epsilon$ therefore gives the desired bound.

**Key facts.** `FABL.stableInfluence_le_influence`, `FABL.stableInfluence_one_eq_influence`.
