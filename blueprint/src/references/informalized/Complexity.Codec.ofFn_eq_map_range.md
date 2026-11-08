<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Complexity/SpaceComplexity/Codec/Valid.lean :: Complexity.Codec.ofFn_eq_map_range -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Finite Function List as a Range Map

**Claim.** For any type $\beta$, function $g:\mathbb{N}\to\beta$, and natural number $m$, the list of values $g(0),g(1),\ldots,g(m-1)$ is the image under $g$ of the list $0,1,\ldots,m-1$.

**Proof.** The two lists have the same length, namely $m$. For each index $i<m$, the entry of the list built from the finite function is $g(i)$, since its $i$th argument is the natural number represented by that finite index. The $i$th entry of the mapped range list is also $g(i)$: the $i$th entry of `List.range m` is $i$, and mapping applies $g$ to it. Thus the lists agree entry by entry, and hence are equal.
