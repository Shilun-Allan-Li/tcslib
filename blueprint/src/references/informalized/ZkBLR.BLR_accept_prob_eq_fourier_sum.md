<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/BLR/ZkBLR.lean :: ZkBLR.BLR_accept_prob_eq_fourier_sum -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Fourier formula for BLR acceptance

**Claim.** The BLR acceptance probability is the average, over twists $j$, of the Fourier sums of squared coefficient magnitudes times the real parts of those coefficients.

**Proof.** For each pair $x,y$, write the test defect as $a=f(x+y)-f(x)-f(y)$ in $\mathbb Z_k$. The character orthogonality identity (`ZkBLR.indicator_eq_char_sum_re`) expresses the indicator that $a=0$ as $1/k$ times the sum over $j\in\mathbb Z_k$ of the real parts of the characters $\omega_k^{ja}$. Summing this identity over all pairs converts the acceptance count into character sums.

Fix a twist $j$. The character of the defect factors into the lifted character at $x+y$ and the conjugates of the lifted characters at $x$ and $y$: this follows from multiplicativity of the root character under addition and from conjugation corresponding to negation (`ZkFourier.toOmega_add`, `ZkFourier.toOmega_neg`). The triple-product Fourier identity (`ZkBLR.triple_product_fourier`) then rewrites the doubly averaged complex sum as the sum over frequencies $s$ of the squared magnitudes of the Fourier coefficients times their complex conjugates. Taking real parts changes each conjugate into the real part of the coefficient, while the two averaging denominators contribute the factor $k^{2n}$. Finally, interchange the finite sums and cancel the normalization by the number $(k^n)^2$ of input pairs. The resulting expression is precisely the stated Fourier formula.

**Key facts.** `ZkBLR.indicator_eq_char_sum_re`, `ZkBLR.triple_product_fourier`, `ZkFourier.toOmega_add`, `ZkFourier.toOmega_neg`.
