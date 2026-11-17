<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/Randomized/RandomWalkMixing.lean :: Randomized.RegularMultigraph.isStationary_iff_eq_uniform -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Uniqueness of the Stationary Uniform Distribution

**Claim.** Under connectedness and nonbipartiteness, a normalized rational stationary distribution is uniform, and the uniform distribution is stationary.

**Proof.** For the reverse implication, the uniform distribution is stationary (`uniform_isStationary`). For the forward implication, connectedness and nonbipartiteness provide a time $k$ at which every transition probability is at least $1/|V|^{10|V|}$; more precisely, this lower bound contracts the excess above uniform for every normalized distribution (`exists_uniformExcess_walkDist_le`). Stationarity implies that the distribution is unchanged after $k$ steps (`IsStationary.walkDist_eq`). Thus its uniform excess is at most $(1-1/|V|^{10|V|})$ times itself. The excess is nonnegative for a normalized distribution (`uniformExcess_nonneg`), so this inequality forces the excess to be zero.

The bound of each coordinate above uniform by the uniform excess (`le_uniformExcess`) now shows that every coordinate is at most $1/|V|$. Since the coordinates sum to $1$, the nonnegative deficits $1/|V|-p(v)$ also sum to zero, using the normalization identity (`sum_sub_inv_card`). A finite sum of nonnegative terms can be zero only if each term is zero. Therefore every coordinate equals $1/|V|$, as required.

**Key facts.** `Randomized.RegularMultigraph.uniform_isStationary`, `Randomized.RegularMultigraph.exists_uniformExcess_walkDist_le`, `Randomized.RegularMultigraph.IsStationary.walkDist_eq`, `Randomized.uniformExcess_nonneg`, `Randomized.le_uniformExcess`, `Randomized.sum_sub_inv_card`.
