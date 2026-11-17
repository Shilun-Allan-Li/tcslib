<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter01/FunctionsAsMultilinearPolynomials.lean :: FABL.expect_sign_values_eq_int_mul_two_inv_pow -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Mean of a Sign-Valued Function

**Claim.** If a function on a finite nonempty set of size $2^m$ takes only the values $-1$ and $1$, then its uniform mean is $z\,2(2^{-1})^m$ for some integer $z$.

**Proof.** Let $N$ be the number of points at which $g=-1$. At each point, $g$ equals $1-2\mathbf{1}_{\{g=-1\}}$, so summing over the domain gives $\sum_x g(x)=|\Omega|-2N=2^m-2N$. The uniform mean is therefore $(2^m-2N)/2^m$. Since $m\ge 1$, we can rewrite this as $\bigl(2^{m-1}-N\bigr)\,2/2^m$, which is the claimed form with the integer $z=2^{m-1}-N$.
