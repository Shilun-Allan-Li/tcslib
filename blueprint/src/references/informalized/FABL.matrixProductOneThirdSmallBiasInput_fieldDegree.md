<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/MatrixProductVerification.lean :: FABL.matrixProductOneThirdSmallBiasInput_fieldDegree -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One-Third Input Field Degree

**Claim.** For every positive integer $n$, the field degree of the input with output dimension $n$ and bias $1/3$ equals $\max\{1,\lceil\log_2(3n)\rceil\}$.

**Proof.** The field degree is the maximum of $1$ and the base-two ceiling logarithm of the input's scale. The scale of this one-third input is $3n$; substituting that value gives exactly $\max\{1,\lceil\log_2(3n)\rceil\}$.

**Key facts.** `FABL.matrixProductOneThirdSmallBiasInput_scale`.
