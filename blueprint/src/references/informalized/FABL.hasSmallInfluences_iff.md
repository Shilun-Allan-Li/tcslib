<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Pseudorandomness/StableInfluences.lean :: FABL.hasSmallInfluences_iff -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Small influences at zero noise

**Claim.** The stable influences at noise parameter $1$ are all at most $\varepsilon$ exactly when every coordinate influence is at most $\varepsilon$.

**Proof.** By definition, setting the noise parameter to $1$ makes the stable-influence parameter $1-0=1$. At this parameter, stable influence equals coordinate influence (`stableInfluence_one_eq_influence`). Substituting this identity into the two definitions gives the stated equivalence.

**Key facts.** `FABL.stableInfluence_one_eq_influence`.
