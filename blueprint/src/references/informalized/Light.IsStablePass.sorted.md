<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/Programs/Util/StablePass.lean :: Light.IsStablePass.sorted -->
<!-- origin: no source citation; informalized directly from the Lean proof -->
<!-- model: gpt-6-luna; confidence: high -->

# Sorted Keys After a Stable Pass

**Claim.** If the input has nondecreasing $g$-values, all of them below $B$, and the output is a stable pass ordered by $k$, then the values $k(i)B+g(i)$ along the output are nondecreasing.

**Proof.** Take any two output positions $a<b$. Each position is assigned to some input position: surjectivity of the position map (`exists_sortPos_eq`) supplies indices $i,j$ whose prescribed positions are $a,b$. The placement condition identifies the output entries there with the input entries at $i,j$. Since $a<b$, their prescribed positions are strictly ordered. The ordering criterion for stable-pass positions (`sortPos_lt_sortPos_iff`) then gives either $k(\pi_i)<k(\pi_j)$, or equal keys with $i<j$; the key-at-position identity (`keyAt_eq`) translates the keys to those of the entries themselves.

In the strict-key case, $g(\pi_i)<B$ ensures that the entire block with key $k(\pi_i)$ precedes the next key block: $(k(\pi_i)+1)B\le k(\pi_j)B$. Hence $k(\pi_i)B+g(\pi_i)\le k(\pi_j)B+g(\pi_j)$. In the equal-key case, the input's nondecreasing $g$-values and $i<j$ give $g(\pi_i)\le g(\pi_j)$, so adding the common key contribution gives the same desired inequality. Thus every pair of output positions in increasing order has nondecreasing combined values.

**Key facts.** `Light.exists_sortPos_eq`, `Light.keyAt_eq`, `Light.sortPos_lt_sortPos_iff`.
