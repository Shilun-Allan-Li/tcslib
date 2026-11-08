<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/BLR/LowDegree.lean :: LowDegreeTest.gowers_U2_eq_L2_conv -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# The $U^2$ norm and convolution

**Claim.** The fourth power of the $U^2$ norm of $f$ equals the squared $L^2$ norm of its self-convolution.

**Proof.** Expand the order-two Gowers product. For each base point $x$ and directions $h_0,h_1$, its four factors are $f(x)$, $f(x\oplus h_0)$, $f(x\oplus h_1)$, and $f((x\oplus h_1)\oplus h_0)$. In the average over the directions, change variables from $(h_0,h_1)$ to $(h,z)$ with $h=h_0$ and $z=x\oplus h_1$. This is a bijection, with inverse $h_0=h$ and $h_1=x\oplus z$. Using commutativity of XOR (`xor_vec_comm`), the product becomes $f(x)f(x\oplus h)f(z)f(z\oplus h)$. Averaging first over $h$ and $z$ identifies the expression with the average over $x$ of $\bigl(\mathbb E_y[f(y)f(x\oplus y)]\bigr)^2$, which is the squared $L^2$ norm of $f*f$.

**Key facts.** `LowDegreeTest.xor_vec_comm`.
