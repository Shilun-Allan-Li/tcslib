<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter06/Gowers.lean :: FABL.expect_mul_add_eq_mul_expect -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Expectation of a Translated Product

**Claim.** For independent uniform cube points $x,h$, the expectation of $a(x)b(x+h)$ factors as $(\mathbb E a)(\mathbb E b)$.

**Proof.** First exchange the order of the two finite uniform averages, obtaining the average over $x$ of the average over $h$ of $a(x)b(x+h)$. For each fixed $x$, translation by $x$ is a bijection of the cube, so as $h$ ranges uniformly, $x+h$ is uniform as well. The inner average is therefore $a(x)\mathbb E[b]$. Averaging this over $x$ gives $(\mathbb E a)(\mathbb E b)$ by factorization of finite uniform averages.
