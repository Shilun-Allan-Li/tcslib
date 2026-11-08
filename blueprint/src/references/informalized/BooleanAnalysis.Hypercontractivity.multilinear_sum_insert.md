<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/RandomVariables/Basic.lean :: BooleanAnalysis.Hypercontractivity.multilinear_sum_insert -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Splitting a Multilinear Sum

**Claim.** For a finite set $s$ and an index $i\notin s$, the multilinear sum over subsets of $s\cup\{i\}$ splits into the contribution from subsets omitting $i$ and $X_i(\omega)$ times the contribution from subsets containing $i$.

**Proof.** Partition the subsets of $s\cup\{i\}$ according to whether they contain $i$. The subsets omitting $i$ are exactly the subsets of $s$. Each subset containing $i$ is uniquely $T\cup\{i\}$ for a subset $T\subseteq s$. Because $i\notin s$, the product indexed by $T\cup\{i\}$ factors as $X_i(\omega)\prod_{j\in T}X_j(\omega)$. Summing the two parts gives the asserted identity; factoring the common $X_i(\omega)$ from the second sum yields the displayed form.
