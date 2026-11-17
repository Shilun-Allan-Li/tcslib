<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter09/OneBitHypercontractivity.lean :: FABL.exists_uniformLpNorm_dual -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# A dual function attaining the norm

**Claim.** For finite nonempty $\Omega$ and Hölder-conjugate exponents $p,q$, there is a function with uniform $p$-norm at most one whose uniform inner product with $f$ equals the uniform $q$-norm of $f$.

**Proof.** Let $N=|\Omega|>0$ and regard $F(x)=|f(x)|$ as a nonnegative real-valued function. The finite-space $L^p$ duality theorem, in its greatest-element form (`NNReal.isGreatest_Lp`), supplies a nonnegative function $G$ with $\sum_x G(x)^p\le1$ and $\sum_x |f(x)|G(x)=(\sum_x|f(x)|^q)^{1/q}$. Define $c=N^{1/p}$ and set $g(x)=c\,\operatorname{sgn}(f(x))G(x)$. Since $|\operatorname{sgn}(f(x))|\le1$, we have $|g(x)|\le cG(x)$; raising to the nonnegative power $p$ and averaging gives $\mathbb E|g|^p\le c^pN^{-1}=1$. Taking the $1/p$ power shows that the uniform $p$-norm of $g$ is at most one. For the inner product, the identity $f(x)\operatorname{sgn}(f(x))=|f(x)|$ gives $\langle f,g\rangle_u=(c/N)\sum_x|f(x)|G(x)$. Hölder conjugacy implies $1/p+1/q=1$, so $c/N=N^{-1/q}$. Thus this inner product equals $((1/N)\sum_x|f(x)|^q)^{1/q}$, the uniform $q$-norm of $f$.

**Caveat.** The proof invokes the finite-space duality result `NNReal.isGreatest_Lp`, which is not included in the supplied upstream list; its statement is described here as it is used by the proof.
