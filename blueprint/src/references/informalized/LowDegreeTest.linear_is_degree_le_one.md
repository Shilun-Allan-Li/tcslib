<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/BLR/LowDegree.lean :: LowDegreeTest.linear_is_degree_le_one -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Linearity implies degree at most one

**Claim.** A Boolean function that respects componentwise XOR has degree at most one: every order-two Gowers product of its sign lift equals $1$.

**Proof.** Linearity implies that the sign lift converts XOR of inputs into multiplication: $(-1)^{f(a\oplus b)}=(-1)^{f(a)}(-1)^{f(b)}$, using the sign-of-XOR identity (`BoolToPM1_xor`). Apply this relation to the vertices appearing in the order-two product: $x\oplus h_1$, $x\oplus h_2$, and $(x\oplus h_2)\oplus h_1$. The recursive formula for the order-two product (`gowers_product_succ`) combines these with the base value at $x$. Substituting their factorizations, each sign-lift value occurs an even number of times. Since each is $1$ or $-1$, their total product is $1$, as required.

**Key facts.** `BoolFourier.BoolToPM1_xor`, `LowDegreeTest.gowers_product_succ`.
