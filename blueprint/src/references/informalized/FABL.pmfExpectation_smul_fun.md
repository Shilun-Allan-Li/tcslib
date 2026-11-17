<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/GeneralizedFourierFormulas.lean :: FABL.pmfExpectation_smul_fun -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Scaling a Finite Expectation

**Claim.** For a finite probability space, the expectation of the pointwise scalar multiple $cf$ equals $c$ times the expectation of $f$.

**Proof.** At each point, scalar multiplication of the real-valued function is ordinary multiplication, so $(c\mathbin{\cdot} f)(x)=c f(x)$. The expectation formula for a pointwise constant multiple (`pmfExpectation_const_mul`) then gives the result directly.

**Key facts.** `FABL.pmfExpectation_const_mul`.
