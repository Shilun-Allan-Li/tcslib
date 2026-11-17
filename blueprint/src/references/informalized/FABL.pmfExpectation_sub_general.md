<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/GeneralizedFourierFormulas.lean :: FABL.pmfExpectation_sub_general -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Linearity of Expectation Under Subtraction

**Claim.** For functions $f$ and $g$ on a finite probability space, the expectation of $f-g$ is the expectation of $f$ minus the expectation of $g$.

**Proof.** Write $f-g$ pointwise as $f+(-g)$. Additivity of expectation (`pmfExpectation_add`) makes its expectation the sum of the expectations of $f$ and $-g$. Negation changes the expectation by a minus sign (`pmfExpectation_neg_general`), and the result follows.

**Key facts.** `FABL.pmfExpectation_add`, `FABL.pmfExpectation_neg_general`.
