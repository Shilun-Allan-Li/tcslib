<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter05/LevelOneInequality.lean :: FABL.expect_mul_levelOneLinearForm_eq -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Expectation Against a Linear Form

**Claim.** The expectation of $f(x)$ times the linear form with coefficients $a_i$ equals $\sum_i a_i\widehat f(\{i\})$, where $\widehat f(\{i\})=\mathbb E[f(x)x_i]$.

**Proof.** Expand the linear form inside the product with $f(x)$. Each sign coordinate is the monomial indexed by its singleton, so pointwise the product is $\sum_i a_i f(x)\operatorname{monomial}_{\{i\}}(x)$. Interchange this finite sum with expectation, then pull the constant coefficient $a_i$ outside each average. Each remaining average is precisely the singleton Fourier coefficient.
