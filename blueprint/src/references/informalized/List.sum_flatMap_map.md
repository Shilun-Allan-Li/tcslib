<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Util/List.lean :: List.sum_flatMap_map -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Sum over a Flattened List

**Claim.** Summing $F$ over the concatenation of the lists $g(x)$ for $x$ in $l$ equals the sum, over $x$ in $l$, of the sum of $F$ over $g(x)$.

**Proof.** Induct on $l$. For the empty list, both sums are zero. If $l$ has head $x$ and tail $xs$, flattening gives $g(x)$ followed by the flattening of $xs$. The sum over this concatenation is the sum over $g(x)$ plus the sum over the flattened tail. Applying the induction hypothesis to the tail gives exactly the head contribution plus the sum of the contributions from each tail element, which is the desired expression.
