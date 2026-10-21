<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/Hypercontractivity/Cube/FourthMoment.lean :: BooleanAnalysis.Hypercontractivity.chiS_snoc_with_last -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: claude-opus-4-8; confidence: high -->

# Walsh character under appending a final coordinate

**Claim.** Fix $n$, a set $S \subseteq [n]$ of coordinates, a point $x \in \{0,1\}^n$, and a bit $b$. Form the point $(x,b) \in \{0,1\}^{n+1}$ by appending $b$ as the new last coordinate, and form the index set $S' \subseteq [n+1]$ consisting of the coordinates of $S$ (viewed inside the first $n$ positions of $[n+1]$) together with the new last position $n+1$. Writing $\sigma$ for the sign of a bit, with $\sigma(0)=1$ and $\sigma(1)=-1$, the Walsh character $\chi_{S'}$ evaluated at $(x,b)$ equals $\sigma(b)\,\chi_S(x)$: adjoining the final coordinate to the lifted index set simply multiplies the character by the sign of $b$.

**Proof.** Recall that the Walsh character of an index set $T$ is the product of coordinate signs over $T$,
\[
  \chi_T(y) \;=\; \prod_{i \in T} \sigma(y_i),
\]
where $\sigma(\texttt{0})=1$ and $\sigma(\texttt{1})=-1$. Unfolding this definition reduces the claim to an identity between two products, which we obtain by splitting off the new last coordinate.

1. **The last index is new.** The index set is $S' = \iota(S) \cup \{n{+}1\}$, where $\iota$ is the inclusion of $[n]$ as the first $n$ positions of $[n+1]$ (`Fin.castSucc`). Every index in $\iota(S)$ lies among the first $n$ positions and is therefore distinct from the last position $n{+}1$ (`Fin.castSucc_ne_last`); hence $n{+}1 \notin \iota(S)$, and the union is genuinely the insertion of a fresh element into $\iota(S)$.

2. **Split the product.** Because $n{+}1$ does not already belong to $\iota(S)$, the product defining $\chi_{S'}$ factors with the last-coordinate term pulled out (`Finset.prod_insert`):
\[
  \chi_{S'}(x,b) \;=\; \sigma\big((x,b)_{n+1}\big)\cdot\prod_{j \in \iota(S)} \sigma\big((x,b)_j\big).
\]

3. **Evaluate the appended point.** The point $(x,b)$ is $x$ extended by $b$ (`Fin.snoc`): its last coordinate is $b$ (`Fin.snoc_last`), and its value at the image position $\iota(j)$ of an original index $j$ is just $x_j$ (`Fin.snoc_castSucc`). Thus the isolated factor is $\sigma(b)$, and each factor of the remaining product is $\sigma(x_j)$.

4. **Re-index over $S$.** The inclusion $\iota$ is injective (`Fin.castSucc_inj`), so running the product over the image $\iota(S)$ is the same as running it over $S$ itself (`Finset.prod_image`). Therefore
\[
  \chi_{S'}(x,b) \;=\; \sigma(b)\cdot\prod_{j \in S} \sigma(x_j) \;=\; \sigma(b)\,\chi_S(x),
\]
which is the desired identity.
