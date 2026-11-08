<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/F₂Polynomials/Affine.lean :: FABL.anfEval_affineCoefficients -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Evaluation of affine coefficients

**Claim.** The algebraic normal form with constant coefficient $b$, singleton coefficients $a_i$, and all other coefficients zero evaluates to $b+\sum_i a_i x_i$.

**Proof.** Fix an input $x$. In the defining sum for the evaluation, only the empty set and singleton sets can contribute: the coefficient vanishes for every other set. Thus the sum splits into the empty-set term and the sum over singleton sets; these parts are disjoint. The empty-set term is $b$, since its monomial is the empty product, hence $1$. Reindex the singleton sets by their unique elements $i$. At $\{i\}$, the coefficient is $a_i$ and the monomial is $x_i$. Summing gives $b+\sum_i a_i x_i$, which is the affine function at $x$. Since this holds for every input, the functions agree.
