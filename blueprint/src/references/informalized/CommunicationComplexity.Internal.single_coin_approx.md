<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/CommunicationComplexity/NewmanTheorem/PrivateCoinApproximation.lean :: CommunicationComplexity.Internal.single_coin_approx -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Finite Space Coin Approximation

**Claim.** For a finite probability space and any $\delta>0$, some finite fair-coin tape and map into the space make every event's preimage probability at most its probability plus $\delta$.

**Proof.** Write $k=|\Omega|$, which is positive, and choose a tape length $n$ large enough that $k/2^n\le\delta$. Identify $\Omega$ with $\mathrm{Fin}\,k$ and the set of coin tapes of length $n$ with $\mathrm{Fin}\,N$, where $N=2^n$.

Represent the point probabilities of $\Omega$ as a probability mass function $q$ on $\mathrm{Fin}\,k$: the probability assigned to index $i$ is the measure of the singleton corresponding to $i$. The singleton masses sum to one (\texttt{hasSum\_measure\_singletons}). Use the uniform approximation map from $\mathrm{Fin}\,N$ to $\mathrm{Fin}\,k$, transport it across the two identifications, and call the resulting map $\varphi$.

For each index $i$, the fraction of inputs mapped to $i$ is at most $(q(i))_{\mathbb R}+1/N$ by the per-fiber estimate (\texttt{uniformApprox\_approx}). For a given event $S$, partition its preimage into the fibers corresponding to those indices whose associated points lie in $S$. The cardinality of the preimage, divided by $N$, is therefore at most the sum of the corresponding point probabilities plus $|S|/N$. The preimage measure under the uniform coin-tape distribution equals this cardinality fraction (\texttt{uniformOn\_univ\_measureReal\_eq\_card\_filter}), and the sum of the point probabilities is $\Pr[S]$, by finite additivity expressed through the singleton-preimage decomposition (\texttt{measureReal\_preimage\_finset}). Since $|S|\le k$ and $k/N\le\delta$, the desired bound follows.

**Key facts.** `CommunicationComplexity.FiniteProbabilitySpace.hasSum_measure_singletons`, `CommunicationComplexity.Internal.uniformApprox_approx`, `CommunicationComplexity.uniformOn_univ_measureReal_eq_card_filter`, `CommunicationComplexity.FiniteProbabilitySpace.measureReal_preimage_finset`.
