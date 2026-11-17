<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Applications/KKL/Junta.lean :: BooleanAnalysis.Hypercontractivity.lowInfluence_fourierConcentration -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Low influence Fourier concentration and junta approximation

**Claim.** For a Boolean-valued sign function $f$ and $0<\varepsilon\le1$, the influential-coordinate set $J$ at the specified threshold has size at most $I[f]^3\varepsilon^{-2}9^k$. The Fourier weight on sets of size at most $k$ that are not contained in $J$ is at most $\varepsilon$. If the Fourier weight above degree $k$ is also at most $\varepsilon$, then the total weight outside the degree-$k$ spectrum supported on $J$ is at most $2\varepsilon$, and $f$ is within disagreement probability $\varepsilon$ of a Boolean junta on $J$.

**Proof.** Write $T=I[f]$ and let $\tau$ be the threshold in the theorem. The total influence is nonnegative, since it is the sum of squared-degree Fourier contributions. The standard cardinality estimate for coordinates with influence at least $\tau$ gives $|J|\le T/\tau$. Substitution of the threshold yields the stated bound; when $T=0$, the bound follows directly from the chosen threshold $\tau=1$.

For the low-degree omitted weight, apply the Fourier omission estimate with $\rho=1/3$. Every coordinate outside $J$ has influence at most $\tau$, by the definition of $J$. The estimate then bounds $(1/3)^k$ times the omitted weight by $\tau^{1/2}T$. The threshold was chosen so that $\tau^{1/2}T\le (1/3)^k\varepsilon$; cancelling the positive factor $(1/3)^k$ proves the omitted weight is at most $\varepsilon$.

Now assume the weight above degree $k$ is at most $\varepsilon$. Partitioning all Fourier sets according to whether their size is at most $k$ and whether they lie in $J$ expresses the weight outside the degree-$k$, $J$-supported portion as the sum of the low-degree omitted weight and the tail. It is therefore at most $2\varepsilon$. The Fourier-omission junta theorem supplies a Boolean function depending only on $J$ whose disagreement with $f$ is at most half the Fourier weight outside $J$. That weight is bounded by the preceding total omitted weight, so the disagreement is at most $\varepsilon$.

**Key facts.** `BooleanAnalysis.totalInfluence_eq_sum_sq_deg`, `KKL.influential_coords_card`, `BooleanAnalysis.Hypercontractivity.fourier_omission_le`, `BooleanAnalysis.Hypercontractivity.exists_boolean_junta_of_fourier_omission`.
