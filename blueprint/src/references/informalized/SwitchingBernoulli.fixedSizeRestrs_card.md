<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/LMN/SwitchingBernoulli.lean :: SwitchingBernoulli.fixedSizeRestrs_card -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: claude-opus-4-8; confidence: high -->

# Counting restrictions with a prescribed number of free variables

**Claim.** Fix natural numbers $n$ and $k$. A *restriction* on $n$ variables is a map $\rho \colon \{0,\dots,n-1\} \to \{\ast\} \cup \{0,1\}$ that either fixes each variable to a Boolean value or leaves it free (the value $\ast$), and its *free set* is the set of variables sent to $\ast$. The claim is that the number of restrictions whose free set has cardinality exactly $k$ is $\binom{n}{k}\,2^{\,n-k}$. (In Lean a restriction is the function type $\mathrm{Fin}\,n \to \mathrm{Option}\,\mathrm{Bool}$, with $\ast$ being `none`; the hypothesis $k \le n$ is carried along but plays no role, since the identity holds even when $k > n$, both sides then being $0$.)

**Proof.** The count is organised by first choosing *which* set of variables is free and then filling in Boolean values on the rest. Concretely, the proof partitions the restrictions-with-$k$-free-variables according to their free set, which is one of the $\binom{n}{k}$ size-$k$ subsets of the variables, and shows each block has $2^{\,n-k}$ elements.

1. **Reduction to a direct function count (bookkeeping).** The object $\mathrm{fixedSizeRestrs}(n,k)$ is the set of restrictions $\rho$ with $|\mathrm{freeVars}(\rho)| = k$, where $\mathrm{freeVars}(\rho)$ is the set of variables $i$ with $\rho(i)$ equal to $\ast$. Unfolding the definitions, a restriction *is* a map $\mathrm{Fin}\,n \to \mathrm{Option}\,\mathrm{Bool}$ and $\mathrm{freeVars}(\rho)$ is exactly $\{i : \rho(i) = \mathrm{none}\}$. So it suffices to count the functions $\rho \colon \mathrm{Fin}\,n \to \mathrm{Option}\,\mathrm{Bool}$ for which $\bigl|\{\,i : \rho(i) = \mathrm{none}\,\}\bigr| = k$; the identification of the two descriptions is a routine rewriting of `isNone` as `= none` (`Finset.card_image_of_injective` is used only to transport the count across the identity coercion from the restriction type).

2. **Partition by free set.** Let $S_k$ denote the family of size-$k$ subsets of $\{0,\dots,n-1\}$. For each $s \in S_k$, consider the map that sends a Boolean assignment $f \colon \{i : i \notin s\} \to \{0,1\}$ to the restriction
\[
\rho_f(i) \;=\; \begin{cases} \ast & i \in s,\\ f(i) & i \notin s,\end{cases}
\]
and let $B_s$ be its image. The claim is that the set of restrictions with exactly $k$ free variables is the union $\bigcup_{s \in S_k} B_s$. Indeed, membership is proved both ways: any such $\rho$ has a free set $s$ of size $k$, and setting $f(i) := \rho(i)$ for the fixed positions $i \notin s$ recovers $\rho = \rho_f$; conversely each $\rho_f$ has free set exactly $s$, of size $k$.

3. **Each block is injective image, hence has $2^{\,n-|s|}$ elements.** For a fixed $s$, the map $f \mapsto \rho_f$ is injective: if $\rho_f = \rho_g$, then evaluating at any fixed position $i \notin s$ gives $f(i) = g(i)$, so $f = g$. Therefore $|B_s|$ equals the number of Boolean assignments on the complement of $s$, namely $2^{\,|\{i : i \notin s\}|} = 2^{\,n - |s|}$ (using that the cardinality of the full function space $\{i \notin s\} \to \{0,1\}$ is $2$ raised to the size of the domain).

4. **The blocks are pairwise disjoint.** If $s \neq t$ are two size-$k$ subsets, then $B_s$ and $B_t$ are disjoint: every element of $B_s$ has free set exactly $s$ and every element of $B_t$ has free set exactly $t$, so a common element would force $s = t$. With disjointness in hand, the cardinality of the union is the sum of the block cardinalities (`Finset.card_biUnion`):
\[
\bigl|\{\rho : |\mathrm{freeVars}(\rho)| = k\}\bigr| \;=\; \sum_{s \in S_k} 2^{\,n - |s|}.
\]

5. **Evaluate the sum.** Every $s \in S_k$ has $|s| = k$ by definition of $S_k$, so each summand is the constant $2^{\,n-k}$ and the sum collapses to $|S_k| \cdot 2^{\,n-k}$. The number of size-$k$ subsets of an $n$-element set is $\binom{n}{k}$ (the cardinality of `powersetCard k univ` is $\binom{|{\rm univ}|}{k} = \binom{n}{k}$). Hence the count equals $\binom{n}{k}\,2^{\,n-k}$, which is exactly $\mathrm{numSRestrictions}(n,k)$. $\blacksquare$
