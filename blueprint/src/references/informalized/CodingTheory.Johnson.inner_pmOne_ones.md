<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/ErrorCorrectingCodes/JohnsonBound.lean :: CodingTheory.Johnson.inner_pmOne_ones -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: claude-opus-4-8; confidence: high -->

# Inner Product of the ±1 Embedding with the All-Ones Vector

**Claim.** Let $x$ be a binary word of length $n$ and let $s(x)\in\mathbb{R}^n$ be its $\pm1$ embedding, whose $i$-th coordinate is $-1$ wherever the bit $x_i$ is set and $+1$ wherever it is not. With $\mathbf{1}$ the all-ones vector and $\mathrm{wt}(x)$ the Hamming weight of $x$ (the number of set positions), the Euclidean inner product satisfies $\langle s(x),\mathbf{1}\rangle = n - 2\,\mathrm{wt}(x)$.

**Proof.** The argument evaluates the inner product coordinate by coordinate and then counts.

1. **Reduce to a sum of coordinates.** The real inner product on $\mathbb{R}^n$ is $\langle s(x),\mathbf{1}\rangle = \sum_{i} s(x)_i\,\mathbf{1}_i$, the unweighted sum of coordinatewise products. Since every coordinate of $\mathbf{1}$ equals $1$, each product $s(x)_i\cdot 1$ collapses to $s(x)_i$, which by definition is $-1$ when $x_i$ is set and $+1$ otherwise. Hence
\[
\langle s(x),\mathbf{1}\rangle \;=\; \sum_{i}\bigl(\text{$-1$ if $x_i$ set, else $+1$}\bigr).
\]

2. **Split the sum according to the bit.** Partitioning the index set $\{0,\dots,n-1\}$ into the positions where $x_i$ is set and those where it is not — the content of `Finset.sum_ite` — the sum becomes
\[
\langle s(x),\mathbf{1}\rangle \;=\; (-1)\cdot\bigl|\{i : x_i \text{ set}\}\bigr| \;+\; (+1)\cdot\bigl|\{i : x_i \text{ not set}\}\bigr|.
\]
The first cardinality is by definition $\mathrm{wt}(x)$.

3. **Count the unset positions by complementation.** The set of unset positions is the complement, inside the full index set, of the set of set positions. Because the latter is a subset of all $n$ indices, its complement has cardinality $n - \mathrm{wt}(x)$ (`Finset.card_sdiff`, which needs exactly this inclusion). Here the subtraction is of natural numbers, and casting it to the reals as $(n:\mathbb{R}) - \mathrm{wt}(x)$ is legitimate because $\mathrm{wt}(x)\le n$ — the set positions form a subset of the $n$ indices — so the proof invokes the cast-of-difference lemma `Nat.cast_sub` under this bound.

4. **Finish by arithmetic.** Substituting the two counts,
\[
\langle s(x),\mathbf{1}\rangle \;=\; -\,\mathrm{wt}(x) + \bigl(n - \mathrm{wt}(x)\bigr) \;=\; n - 2\,\mathrm{wt}(x),
\]
as claimed.
