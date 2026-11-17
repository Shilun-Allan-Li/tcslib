<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/LowDegreeJuntaResources.lean :: FABL.lowDegreeJuntaLearningAlgorithm_workCost_isBigO -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Polynomial Work-Cost Bound

**Claim.** For each fixed $k\in\mathbb{N}$ and each learning accuracy $\varepsilon\in[0,1/2]$, the work cost of the low-degree junta learning algorithm, as a function of input dimension $n$, is $O\!\left((n+1)^{\lfloor 3k/4\rfloor+4}\right)$ as $n\to\infty$.

**Proof.** Fix $k$ and the accuracy. The pointwise work-cost bound gives, for every $n$, an upper bound of $4\,\mathrm{juntaTreeCallCount}(k)\,\mathrm{lowDegreeJuntaNodeWorkLinearCoefficient}(k)$ times $(n+1)^{\mathrm{lowDegreeJuntaNodeWorkResourceExponent}(k)$ (Lean: `lowDegreeJuntaLearningAlgorithm_workCost_le`). The prefactor depends on $k$ but not on $n$, so it is a valid constant in the definition of Big-O. Thus the work-cost function is eventually bounded by that constant times the stated comparison function; in fact the bound holds for every $n$. Finally, the resource exponent is $\lfloor 3k/4\rfloor+4$, yielding the claimed asymptotic order.

**Key facts.** `FABL.lowDegreeJuntaLearningAlgorithm_workCost_le`.
