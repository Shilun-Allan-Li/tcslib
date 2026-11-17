<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/LowDegreeJuntaResources.lean :: FABL.lowDegreeJuntaNodeWorkBound_le_linearConfidence -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Node Work Bound

**Claim.** For every $n$, subset $P\subseteq[n]$, and natural numbers $k,b$, the node work bound at the dyadic node failure parameter is at most its stated work coefficient times $(n+1)^{\lfloor3k/4\rfloor+4}(b+1)$.

**Proof.** Let $M$ be the restricted sample count, let $E$ be the node random-example count, and let $B=(n+1)^{\lfloor3k/4\rfloor+3}$. The restricted-sample, random-example, and node-analysis estimates bound these quantities respectively by their linear coefficients times $B(b+1)$ ( `lowDegreeJuntaRestrictedSampleCount_le_linearConfidence`, `lowDegreeJuntaNodeRandomExamples_le_linearConfidence`, and `lowDegreeJuntaNodeAnalysisWorkBound_le_linearConfidence`). Also $|P|+1\le n+1$. In the work bound, the sample-work term is $E(|P|+1)+M$, so it is at most $E(n+1)+M$. The work exponent is one larger than the base exponent, giving $(n+1)^{\lfloor3k/4\rfloor+4}=B(n+1)$. Thus the term $E(n+1)$ fits under the lifted random-example bound, while the terms $E$, $M$, and the analysis work fit under their corresponding bounds lifted from $B$ to $B(n+1)$; this lift is valid since $n+1\ge1$. Adding these estimates and collecting coefficients gives the stated work coefficient.

**Key facts.** `FABL.lowDegreeJuntaRestrictedSampleCount_le_linearConfidence`, `FABL.lowDegreeJuntaNodeRandomExamples_le_linearConfidence`, `FABL.lowDegreeJuntaNodeAnalysisWorkBound_le_linearConfidence`.
