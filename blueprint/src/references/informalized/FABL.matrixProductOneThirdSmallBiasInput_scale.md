<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/MatrixProductVerification.lean :: FABL.matrixProductOneThirdSmallBiasInput_scale -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One-Third Input Scale

**Claim.** For every positive integer $n$, the scale of the input with output dimension $n$ and bias $1/3$ is $3n$.

**Proof.** The scale is the ceiling quotient of the output dimension times the denominator by the numerator. For this input those values are $n$, $3$, and $1$, respectively. Dividing $3n$ by $1$ leaves $3n$, so the scale is $3n$.
