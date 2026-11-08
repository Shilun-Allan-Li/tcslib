<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/MatchingMomentCombinatorics.lean :: FABL.perfectMatchingPartner_ne -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Matching partners are distinct

**Claim.** In a perfect matching on $2m$ vertices, the partner of any vertex $v$ differs from $v$.

**Proof.** The partner is adjacent to $v$. If it were equal to $v$, this would give a loop at $v$, contradicting that the matching is loopless.

**Key facts.** `FABL.perfectMatchingPartner_adj`.
