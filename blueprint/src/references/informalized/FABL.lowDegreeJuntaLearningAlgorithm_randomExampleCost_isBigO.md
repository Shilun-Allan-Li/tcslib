<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/LowDegreeJuntaResources.lean :: FABL.lowDegreeJuntaLearningAlgorithm_randomExampleCost_isBigO -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial Random-Example Cost Bound

**Claim.** For every integer $k\ge 0$ and every accuracy parameter in $[0,1/2]$, the low-degree junta learning algorithm's random-example cost is $O\bigl((n+1)^{\lfloor 3k/4\rfloor+3}\bigr)$ as $n\to\infty$.

**Proof.** The pointwise resource bound for the learner states that, for every dimension $n$, its random-example cost is at most $4$ times the number of calls made by the junta tree, times a coefficient depending only on $k$, times $(n+1)^{\mathrm{lowDegreeJuntaNodeBaseResourceExponent}(k)$ (\texttt{lowDegreeJuntaLearningAlgorithm\_randomExampleCost\_le}). Fix $k$. The prefactor is therefore a constant independent of $n$ (and the bound is uniform in the accuracy parameter). By the definition of big-O with an eventual bound, this pointwise inequality gives the asserted asymptotic estimate. Finally, the base resource exponent is $\mathrm{lowDegreeJuntaCutoff}(k)+3=\lfloor 3k/4\rfloor+3$, yielding the stated power.

**Key facts.** `FABL.lowDegreeJuntaLearningAlgorithm_randomExampleCost_le`.
