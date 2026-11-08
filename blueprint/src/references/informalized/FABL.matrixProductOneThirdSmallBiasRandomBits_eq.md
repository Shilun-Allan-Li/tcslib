<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/LearningAndTesting/MatrixProductVerification.lean :: FABL.matrixProductOneThirdSmallBiasRandomBits_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# One-Third Input Random Bits

**Claim.** For every positive integer $n$, twice the field degree of the input with output dimension $n$ and bias $1/3$ equals the number of random bits specified for dimension $n$.

**Proof.** The field degree of the one-third input equals the specified small-bias degree. Replacing each of the two field-degree terms by that degree gives its sum with itself, which is the definition of the specified random-bit count.

**Key facts.** `FABL.matrixProductOneThirdSmallBiasInput_fieldDegree`.
