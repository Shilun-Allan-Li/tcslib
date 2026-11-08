<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/PrivateCoinApproximation.lean :: CommunicationComplexity.Internal.product_coin_approx -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Product-Space Coin Approximation

**Claim.** For finite probability spaces $\Omega_X,\Omega_Y$ and $\delta>0$, there are coin-tape maps into each space such that the product map gives every event probability at most its original probability plus $\delta$.

**Proof.** Apply the single-space coin approximation to $\Omega_X$ and $\Omega_Y$, each with error $\delta/2$. This gives lengths and maps $\varphi_X,\varphi_Y$ whose preimages of any event have probability at most the event's probability plus $\delta/2$.

For each $a\in\Omega_X$, let $S_a=\{b\in\Omega_Y:(a,b)\in S\}$. The preimage of $S$ under the product map is the union, over $a$, of the rectangles $\varphi_X^{-1}(\{a\})\times\varphi_Y^{-1}(S_a)$. These rectangles are pairwise disjoint because a coin tape under $\varphi_X$ cannot map to two distinct values. Decomposing the measure over these rectangles and using the product formula for rectangle measures (\texttt{measureReal\_iUnion\_fintype}; \texttt{measureReal\_prod}) expresses the preimage probability as $\sum_a p_X(a)\,\Pr[\varphi_Y^{-1}(S_a)]$, where $p_X(a)=\Pr[\varphi_X^{-1}(\{a\})]$.

Apply the approximation guarantee for $\varphi_Y$ on each slice. Since the $p_X(a)$ are nonnegative and sum to one, this bounds the preimage probability by $\sum_a p_X(a)\Pr[S_a]+\delta/2$. The sum-to-one identity follows by decomposing the whole coin-tape space into the fibers of $\varphi_X$; equivalently, its preimage of the entire finite target has measure one.

It remains to compare the weighted slice probabilities under $p_X$ with those under the original distribution $q_X(a)=\Pr[\{a\}]$. The approximation guarantee for $\varphi_X$ implies, for every subset $T\subseteq\Omega_X$, that $\sum_{a\in T}p_X(a)\le\sum_{a\in T}q_X(a)+\delta/2$: express each side as the measure of the corresponding preimage or finite set. The weighted-sum estimate (\texttt{weighted\_sum\_approx}) then applies to the slice weights $g(a)=\Pr[S_a]$, which lie between zero and one. It gives $\sum_a p_X(a)\Pr[S_a]\le\sum_a q_X(a)\Pr[S_a]+\delta/2$. Finally, the original event is the disjoint union of the slices $\{a\}\times S_a$, so the last weighted sum is exactly $\Pr[S]$, by finite disjoint-union additivity and the product formula for rectangles. Combining the two error terms proves the bound. The single-space approximation used at the outset is (\texttt{single\_coin\_approx}).

**Key facts.** `CommunicationComplexity.Internal.single_coin_approx`, `CommunicationComplexity.FiniteProbabilitySpace.measureReal_iUnion_fintype`, `CommunicationComplexity.FiniteProbabilitySpace.measureReal_prod`, `CommunicationComplexity.Internal.weighted_sum_approx`.
