<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: ../FABL/FABL/Chapter08/BiasedThresholdPhenomena.lean :: FABL.powersetCard_univ_nonempty -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Nonempty family of fixed-size subsets

**Claim.** For $k\in\{0,\ldots,n\}$, the family of $k$-element subsets of an $n$-element set is nonempty.

**Proof.** A finite set has a $k$-element subset exactly when $k$ is at most its cardinality (\texttt{Finset.powersetCard\_nonempty}). Here the underlying set is the full set of indices $\{0,\ldots,n-1\}$, whose cardinality is $n$. Because $k\in\mathrm{Fin}(n+1)$, we have $k\leq n$, and therefore the family is nonempty.
