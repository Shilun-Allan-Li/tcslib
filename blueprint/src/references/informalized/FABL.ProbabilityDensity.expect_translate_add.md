<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/FoolingF₂Polynomials/Fooling.lean :: FABL.ProbabilityDensity.expect_translate_add -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Translation invariance of uniform expectation

**Claim.** For a function $f:\mathbb F_2^n\to\mathbb R$ and a vector $z\in\mathbb F_2^n$, the uniform expectation of $x\mapsto f(x+z)$ equals the uniform expectation of $f$.

**Proof.** Translation by $z$ is a bijection of the cube, with inverse translation by $-z$. A uniform average over a finite set is unchanged by reindexing along a bijection. Under the reindexing $x\mapsto x+z$, the summand $f(x+z)$ becomes $f(x)$, giving the claimed equality.
