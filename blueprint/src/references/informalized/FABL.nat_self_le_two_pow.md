<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/LearningConsequencesResources.lean :: FABL.nat_self_le_two_pow -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Natural number bounded by a power of two

**Claim.** For every natural number $m$, one has $m\le 2^m$.

**Proof.** The successor bound gives $m+1\le 2^m$ (`nat_succ_le_two_pow`). Since $m\le m+1$, transitivity yields $m\le 2^m$.

**Key facts.** `FABL.nat_succ_le_two_pow`.
