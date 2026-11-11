<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Applications/KKL/Junta.lean :: BooleanAnalysis.Hypercontractivity.friedgut_junta -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Friedgut’s Junta Theorem

**Claim.** There is an absolute constant $C>0$ such that every Boolean $\{-1,1\}1$-valued function and every $0<\epsilon\leq1$ admit a junta whose coordinate set has size at most $\exp(C I[f]/\epsilon)$, and whose Fourier spectrum outside subsets of that set of degree at most $I[f]/\epsilon$ has squared weight at most $2\epsilon$; the junta is itself Boolean-valued and is $\epsilon$-close to the original function.

**Proof.** 1. Choose $C=11$, write $I=I[f]$, and set $t=I/\epsilon$. The identity expressing total influence as the sum of degree-weighted squared Fourier coefficients, `totalInfluence_eq_sum_sq_deg`, shows that $I\geq0$. Let $k=\lfloor t\rfloor$. Then $k\leq t<k+1$, and the integer degree of a set is at most $t$ exactly when it is at most $k$.

2. The degree-tail estimate `fourierWeightAbove_le_totalInfluence_div_succ` bounds Fourier weight above degree $k$ by $I/(k+1)$. Since $t<k+1$ and $t=I/\epsilon$, this is at most $\epsilon$. Apply the low-influence Fourier concentration theorem `lowInfluence_fourierConcentration` at degree $k$ and parameter $\epsilon$. It supplies a coordinate set $J$ and a Boolean-valued function $h$ that is a junta on $J$, is within $\epsilon$ of $f$, and has at most $2\epsilon$ Fourier weight outside the sets contained in $J$ of degree at most $k$. By the degree equivalence above, this is precisely the spectral bound in the claim.

3. The same theorem bounds the size of $J$ by $I^3\epsilon^{-2}9^k$. Rewrite $I^3\epsilon^{-2}=\epsilon t^3\leq t^3\leq e^{3t}$, using $\epsilon\leq1$, $t\geq0$, and $1+t\leq e^t$. Also, $9^k=e^{k\log 9}\leq e^{8t}$, since $k\leq t$ and $\log 9\leq8$. Thus $|J|\leq e^{11t}=\exp(11I/\epsilon)$, proving the size bound with the chosen constant.

**Key facts.** `BooleanAnalysis.totalInfluence_eq_sum_sq_deg`, `BooleanAnalysis.Hypercontractivity.fourierWeightAbove_le_totalInfluence_div_succ`, `BooleanAnalysis.Hypercontractivity.lowInfluence_fourierConcentration`.
