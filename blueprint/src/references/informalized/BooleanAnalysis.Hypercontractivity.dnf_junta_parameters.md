<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Applications/KKL/DNF.lean :: BooleanAnalysis.Hypercontractivity.dnf_junta_parameters -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Parameters for DNF Approximation

**Claim.** There is a universal constant $C>0$ such that for every positive integer $w$ and every $0<\varepsilon\le1/2$, one can choose a natural number $t$ making both the dyadic error bound and the stated width-dependent growth bound hold.

**Proof.** Let $L=\log 2$, $M=\log 9$, and choose $C=2+(6+720M)/L$, which is positive. Set $\ell=\log(1/\varepsilon)$ and $q=\ell/L$. Because $\varepsilon\le1/2$, we have $q\ge1$. Round upward to $m=\lceil q\rceil$ and take $t=m+3$. The ceiling bounds give $q\le m\le q+1$, and hence $t+1\le6q$.

Since $qL=\ell$, the upward rounding ensures $8(1/2)^t\le\varepsilon$: in exponential form the left side is $\exp(3L-tL)$, which is at most $\exp(-\ell)=\varepsilon$.

For the second inequality, use $e^u\ge1+u$ to bound $(2w)^3\le\exp(6w)$. Put $K=120w(t+1)$. The bounds $w\ge1$ and $t+1\le6q$ imply
\[
6w+2\ell+KM\le \ell Cw.
\]
Indeed, the three terms on the left are bounded respectively by $6qw$, $2\ell w$, and $720wqM$, whose sum is exactly $\ell Cw$. Rewriting the left side of the desired inequality as an exponential, using $\ell=\log(1/\varepsilon)$ and $M=\log 9$, now gives
\[
(2w)^3\varepsilon^{-2}9^K\le \exp(\ell Cw)=(1/\varepsilon)^{Cw}.
\]
Thus this choice of $t$ satisfies both bounds.
