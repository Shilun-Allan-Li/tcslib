<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/RandomVariables/Tensorization.lean :: BooleanAnalysis.Hypercontractivity.Tensorization.lintegral_minkowski -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Minkowski Inequality for Product Integrals

**Claim.** For measurable nonnegative $f$ on a product of probability spaces and $r\ge1$, the $L^r$ norm in the second variable of the first-variable integral is at most the first-variable integral of the $L^r$ norms in the second variable.

**Proof.** If $r=1$, the two sides agree by Tonelli's theorem, which permits exchanging the order of integration. Suppose $r>1$, and let $q$ be the Hölder conjugate of $r$. Define $H(y)=\int f(x,y)\,d\mu(x)$ and truncate it by $U_n(y)=\min(H(y),n)$. Put $C_n=\int U_n(y)^r\,d\nu(y)$ and let $T=\int (\int f(x,y)^r\,d\nu(y))^{1/r}\,d\mu(x)$.

Each $C_n$ is finite because $U_n\le n$ and $\nu$ is a probability measure. For fixed $n$, use $g(y)=U_n(y)^{r-1}$ as a test function. Hölder's inequality in $y$ bounds $\int f(x,y)g(y)\,d\nu(y)$ by $(\int f(x,y)^r\,d\nu(y))^{1/r}C_n^{1/q}$. Tonelli exchanges the integrals of $fg$, while $U_n\le H$ gives $C_n=\int U_n^r\,d\nu\le\int Hg\,d\nu$. Integrating the Hölder bound in $x$ therefore gives $C_n\le T C_n^{1/q}$. If $C_n=0$, the desired bound on $C_n^{1/r}$ is immediate; otherwise, divide by $C_n^{1/q}$ to obtain $C_n^{1/r}\le T$.

Equivalently, $C_n\le T^r$. As $n$ increases, $U_n$ increases pointwise to $H$. Monotone convergence applied to $U_n^r$ gives $\int H^r\,d\nu=\sup_n C_n\le T^r$. Taking the $r$-th root proves the inequality.
