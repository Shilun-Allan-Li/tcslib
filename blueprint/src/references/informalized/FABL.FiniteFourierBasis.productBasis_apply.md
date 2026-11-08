<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/ProductFourierBases.lean :: FABL.FiniteFourierBasis.productBasis_apply -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation of the product basis

**Claim.** For every multi-index $a\in\iota^n$, the product basis vector indexed by $a$ is the function $x\mapsto\prod_{i=1}^n B_{a_i}(x_i)$.

**Proof.** The product basis is obtained from the family of product functions by extending that family to a basis. By construction, its value at an index $a$ is the corresponding product function. Unfolding that definition identifies the value with the function $x\mapsto\prod_i B_{a_i}(x_i)$.
