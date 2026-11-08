# Published pair-component bound comparator

The newly included PolyTimeBlockLoop source contains the public existing theorem
`Complexity.length_pair_components_le` at captured line207:

```lean
theorem length_pair_components_le (y : List Bool) :
    2 * (pairFstD y).length + (pairSndD y).length ≤ y.length
```

The current approved Hardness body at captured line6837 is:

```lean
private lemma clA5Pair_sizes (w : List Bool) :
    (clHeaderField 0 w).length ≤ w.length ∧ (clHeaderTail 1 w).length ≤ w.length
```

At the mathematical/source-contract level, the weighted public bound is stronger
than the two component inequalities after identifying the own projections with
`pairFstD`/`pairSndD`. Current source instead proves the inequalities using Encoding's
published `eq_pairEncode_of_pairDecode` and `length_pairEncode` equations. Both complete
bodies and homes are retained among the25 full inputs.

This is an available-elsewhere comparator, not a claim that no public bound exists.
The earlier maintainer import crosscheck reports PolyTimeBlockLoop absent; the only
new Hardness import is PolyTimePrefix, and BlockLoop imports Prefix rather than vice
versa. This task did not run a compiled-environment availability probe or an opaque
consumer conversion for this alternative. Refolding opaque public projections would
need their published equations, not an undocumented definitional conversion. A further
frozen-file import would require the user's ruling. No new import/API, source repair,
impossibility, debt acknowledgement or gate-blocker determination is made here; parent
owns the existing approved repair and final reuse-accounting disposition.
