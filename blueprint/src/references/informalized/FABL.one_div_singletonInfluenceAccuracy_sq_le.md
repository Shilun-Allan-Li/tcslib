<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/LearningConsequencesResources.lean :: FABL.one_div_singletonInfluenceAccuracy_sq_le -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Singleton accuracy reciprocal bound

**Claim.** Under the stated sub-square-root regime, the reciprocal square of the singleton accuracy is at most the stated power-of-two bound multiplied by $16$.

**Proof.** Write $\tau$ for the threshold and $P=2^{K(\sqrt{\lceil\log_2(n+1)\rceil}+1)}$, where $K$ is the stated exponent coefficient. The threshold estimate (`one_div_learningConsequencesThreshold_sq_le_two_pow`) gives $\tau^{-2}\le P$. The accuracy is $\min(\tau/4,1/2)$ (`singletonInfluenceAccuracy_value`), so split according to which term is smaller. If $\tau/4\le 1/2$, its reciprocal square is $16\tau^{-2}$, hence at most $16P$. Otherwise the accuracy is $1/2$, whose reciprocal square is $4$; since $P\ge1$, this is at most $16P$.

**Key facts.** `FABL.one_div_learningConsequencesThreshold_sq_le_two_pow`, `FABL.singletonInfluenceAccuracy_value`.
