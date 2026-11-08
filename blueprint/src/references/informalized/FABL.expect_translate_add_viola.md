<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/FoolingF₂Polynomials/ViolaAuxiliary.lean :: FABL.expect_translate_add_viola -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Translation Invariance of Cube Averages

**Claim.** For any real-valued function $F$ on the finite vector space of binary $n$-tuples and any fixed tuple $z$, the uniform average of $F(z+x)$ equals the uniform average of $F(x)$.

**Proof.** Translation by $z$ is a bijection of the finite cube, with inverse translation by $-z$. A uniform average is unchanged when its summation variable is reindexed by a bijection. Thus the average of $F(x+z)$ equals that of $F(x)$; commutativity of addition identifies $F(x+z)$ with $F(z+x)$.
