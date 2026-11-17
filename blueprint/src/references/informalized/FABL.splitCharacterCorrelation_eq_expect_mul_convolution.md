<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter07/AlgebraicPCPP.lean :: FABL.splitCharacterCorrelation_eq_expect_mul_convolution -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Split correlation as averaged convolution

**Claim.** In split coordinates, the split character correlation equals the average over $a$ of the coset average at $a$ multiplied by the normalized convolution of the section sign function with itself, evaluated at $a$.

**Proof.** Expand the correlation as nested uniform averages over $a$, $b$, and $h$. For fixed $a,b$, the two factors involving the section, namely the values at $(0,b)$ and $(0,a+b)$, do not depend on $h$. They therefore factor out of the average over $h$, leaving the coset average at $a$ times those two section values. Now fix $a$ and use the convolution formula: the convolution at $a$ is the average over $b$ of the section value at $b$ times its value at $a+b$. Multiplying this average by the coset average gives exactly the average over $b$ of the preceding expression. Averaging over $a$ proves the identity; the final rearrangement is just associativity and commutativity of real multiplication. The convolution formula used here is `convolution_apply_add`.

**Key facts.** `FABL.convolution_apply_add`.
