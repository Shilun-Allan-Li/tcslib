<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Cube/FourthMoment.lean :: BooleanAnalysis.Hypercontractivity.finset_fin_succ_sum_partition -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: claude-opus-4-8; confidence: high -->

# Splitting a subset-sum by the top coordinate

**Claim.** Fix $n \in \mathbb{N}$ and let $\iota$ denote the inclusion that regards a subset $T \subseteq \{0,\dots,n-1\}$ as the same set of elements inside $\{0,\dots,n\}$ (in Lean, $T \mapsto$ the image of $T$ under `Fin.castSucc`). Then for any real-valued function $\varphi$ on the subsets of $\{0,\dots,n\}$, the total sum $\sum_{S \subseteq \{0,\dots,n\}} \varphi(S)$ equals $\sum_{T \subseteq \{0,\dots,n-1\}} \varphi(\iota(T)) + \sum_{T \subseteq \{0,\dots,n-1\}} \varphi(\iota(T) \cup \{n\})$. The two sums on the right collect exactly the subsets of $\{0,\dots,n\}$ that omit the top element $n$ and those that contain it, respectively.

**Proof.** The argument reorganizes the index set — all subsets of $\{0,\dots,n\}$ — into two disjoint families parametrized by subsets of $\{0,\dots,n-1\}$, and then rewrites each sum over a family as a sum over its parameter.

Write $n$ for the top element $\mathrm{last}(n)$ of $\{0,\dots,n\}$, and for a subset $T \subseteq \{0,\dots,n-1\}$ write $\iota(T)$ for its image inside $\{0,\dots,n\}$ under the order-inclusion $i \mapsto i$ (the map `Fin.castSucc`, which hits every element of $\{0,\dots,n\}$ except $n$). Consider the two maps
\[
  A : T \mapsto \iota(T), \qquad B : T \mapsto \iota(T) \cup \{n\},
\]
each sending a subset of $\{0,\dots,n-1\}$ to a subset of $\{0,\dots,n\}$.

1. **The two families cover everything.** We claim that every $S \subseteq \{0,\dots,n\}$ lies in the image of $A$ or of $B$, so that the collection of all subsets of $\{0,\dots,n\}$ is the union $\operatorname{im} A \cup \operatorname{im} B$. Fix $S$ and let
\[
  T_S \;=\; \{\, i \in \{0,\dots,n-1\} : i \in S \,\}
\]
be the trace of $S$ on the lower coordinates (formally $\{i : \mathrm{castSucc}(i) \in S\}$); this is exactly $\iota^{-1}$ applied to $S$ with the top element discarded. Split on whether $n \in S$.
   - If $n \notin S$, then $S$ contains no copy of the top element, so every element of $S$ is $\mathrm{castSucc}(i)$ for some $i \in \{0,\dots,n-1\}$, and such $i$ lies in $T_S$. Hence $\iota(T_S) = S$ and $S \in \operatorname{im} A$. (The direction "every element of $\{0,\dots,n\}$ is either $n$ or $\mathrm{castSucc}(i)$ for a unique lower $i$" is the exhaustive case analysis `Fin.lastCases`.)
   - If $n \in S$, the same computation gives $\iota(T_S) = S \setminus \{n\}$, so $\iota(T_S) \cup \{n\} = S$ and $S \in \operatorname{im} B$. Here one uses that any element of $S$ other than $n$ is strictly below the top and hence of the form $\mathrm{castSucc}(i)$.

2. **The two families are disjoint.** A set in $\operatorname{im} A$ has the form $\iota(T)$ and therefore does **not** contain $n$ (the inclusion misses the top element), whereas every set in $\operatorname{im} B$ contains $n$ by construction. So if a single set lay in both images, testing membership of $n$ would give a contradiction. Thus $\operatorname{im} A$ and $\operatorname{im} B$ are disjoint.

3. **Summing over a disjoint union.** By Steps 1 and 2 the family of all subsets of $\{0,\dots,n\}$ is the disjoint union $\operatorname{im} A \sqcup \operatorname{im} B$, so the total sum splits (`Finset.sum_union`):
\[
  \sum_{S} \varphi(S) \;=\; \sum_{S \in \operatorname{im} A} \varphi(S) \;+\; \sum_{S \in \operatorname{im} B} \varphi(S).
\]

4. **Each map is injective, so reindex.** The map $A$ is injective: if $\iota(T) = \iota(T')$, then for each lower index $a$ the element $\mathrm{castSucc}(a)$ lies in $\iota(T)$ iff $a \in T$, and likewise for $T'$; since $\mathrm{castSucc}$ is injective these memberships agree, forcing $T = T'$. The map $B$ is injective by the same argument, because adjoining the single top element $n$ does not alter membership of any $\mathrm{castSucc}(a)$. Injectivity lets us rewrite each sum over an image as a sum over its parameter without double-counting (`Finset.sum_image`):
\[
  \sum_{S \in \operatorname{im} A} \varphi(S) = \sum_{T} \varphi(\iota(T)), \qquad
  \sum_{S \in \operatorname{im} B} \varphi(S) = \sum_{T} \varphi(\iota(T) \cup \{n\}).
\]

Substituting these two identities into the splitting of Step 3 yields exactly
\[
  \sum_{S \subseteq \{0,\dots,n\}} \varphi(S)
  = \sum_{T \subseteq \{0,\dots,n-1\}} \varphi(\iota(T))
  + \sum_{T \subseteq \{0,\dots,n-1\}} \varphi(\iota(T) \cup \{n\}),
\]
as claimed. $\qquad\blacksquare$
