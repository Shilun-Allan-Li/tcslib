<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/FoolingF₂Polynomials/Viola.lean :: FABL.isTranslationClosed_f₂PolynomialSignClass -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Translation invariance of the sign class

**Claim.** Translating the input of a function in the degree-at-most-$d$ polynomial sign class produces another function in that class.

**Proof.** Represent the given function as the real sign encoding of a binary-valued function $f$ of algebraic degree at most $d$. For a translation vector $z$, use the translated binary function $x\mapsto f(x+z)$ as the new representative. Translation preserves its function algebraic degree (`FABL.functionAlgebraicDegree_domainTranslate`), so the degree bound remains at most $d$. By the definitions, its real sign encoding is precisely the original function evaluated at $x+z$, giving the desired translated function.

**Key facts.** `FABL.functionAlgebraicDegree_domainTranslate`.
