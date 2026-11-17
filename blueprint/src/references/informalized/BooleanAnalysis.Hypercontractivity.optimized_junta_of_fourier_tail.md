<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Applications/KKL/Junta.lean :: BooleanAnalysis.Hypercontractivity.optimized_junta_of_fourier_tail -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Optimized junta from Fourier tail

**Claim.** Given a Boolean-valued function with positive total influence and the stated Fourier-tail bound, one can find a junta whose size is at most the optimized bound and whose disagreement probability from the original function is at most $\varepsilon$.

**Proof.** Put $I=I[f]$, $\rho=\eta/(2+\eta)$, $p=1+\eta$, and $c=\varepsilon\rho^k$. These are positive where needed, and $0<\rho\le1$. Choose the influential-coordinate set $J$ at threshold $\tau=\exp(p(\log c-\log I))$. The exponent $(1-\rho)/(1+\rho)$ equals $1/p$, so $\tau^{(1-\rho)/(1+\rho)}I=c$. The weighted Fourier-omission estimate (`fourier_omission_le`), applied to this $J$, bounds by $\varepsilon$ the omitted Fourier weight on sets of size at most $k$: outside $J$, every coordinate has influence at most $\tau$ by the definition of $J$, and the identity above makes the estimate exactly $\rho^k$ times that weight at most $c$. Splitting all Fourier sets into those of size at most $k$ and those larger than $k$, the assumed tail bound then shows that the total Fourier weight outside $J$ is at most $2\varepsilon$. The Boolean-junta approximation result (`exists_boolean_junta_of_fourier_omission`) therefore supplies a Boolean-valued junta $h$ depending only on $J$, with disagreement probability at most half this omitted weight, hence at most $\varepsilon$. Finally, the influential-coordinate cardinality bound (`influential_coords_card`) gives $|J|\le I/\tau$. Rewriting the exponential threshold using $\tau^{1/p}=c/I$ yields $I/\tau=I^{2+\eta}/c^{1+\eta}$, which is the asserted size bound.

**Key facts.** `BooleanAnalysis.Hypercontractivity.fourier_omission_le`, `BooleanAnalysis.Hypercontractivity.exists_boolean_junta_of_fourier_omission`, `KKL.influential_coords_card`.
