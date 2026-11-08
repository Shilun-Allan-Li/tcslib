<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter03/LearningTheory/FiniteFamily.lean :: FABL.finiteFamilyFourierEstimatorOutput_evaluationWork -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Estimator evaluation work

**Claim.** For every input, the evaluation work of the resulting Fourier estimator hypothesis is $|\mathcal{F}|(n+1)$.

**Proof.** By definition, evaluation work is the size of the hypothesis support multiplied by $n+1$. The estimator output is constructed with support exactly $\mathcal{F}$, so its evaluation work is $|\mathcal{F}|(n+1)$, independently of the input.
