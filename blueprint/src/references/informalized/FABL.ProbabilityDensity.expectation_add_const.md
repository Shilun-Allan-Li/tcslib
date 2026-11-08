<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/FoolingF₂Polynomials/Viola.lean :: FABL.ProbabilityDensity.expectation_add_const -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Adding a constant to a density expectation

**Claim.** For a probability density $\varphi$, a function $F$, and a real constant $c$, the expectation of $F+c$ under $\varphi$ is the expectation of $F$ under $\varphi$ plus $c$.

**Proof.** By definition, the left side is the uniform expectation of $x\mapsto\varphi(x)(F(x)+c)$. Distribute the product and use linearity of uniform expectation to write this as the expectation of $\varphi F$ plus the expectation of $\varphi c$. Factoring out the constant $c$ from the latter expectation gives $c$ times the uniform expectation of $\varphi$. Since a probability density has uniform expectation one (`ProbabilityDensity.expect_eq_one`), this last term is $c$. The first term is exactly the expectation of $F$ under $\varphi$.

**Key facts.** `FABL.ProbabilityDensity.expect_eq_one`.
