<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/RecursiveNANDComposition.lean :: FABL.pmfExpectation_const_add_general -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Adding a constant inside expectation

**Claim.** For a finite probability mass function, the expectation of $x\mapsto c+f(x)$ is $c$ plus the expectation of $f$.

**Proof.** Regard the function $x\mapsto c+f(x)$ as the sum of the constant function with value $c$ and $f$. Linearity of expectation for sums of functions (`FABL.pmfExpectation_add_fun`) splits the expectation into two terms; the constant term has expectation $c$ (`FABL.pmfExpectation_const`). Combining them gives the claimed formula.

**Key facts.** `FABL.pmfExpectation_add_fun`, `FABL.pmfExpectation_const`.
