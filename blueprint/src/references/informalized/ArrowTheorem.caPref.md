<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/ArrowTheorem.lean :: caPref -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# The c-vs-a ballot of each of the six orderings

**Definition.** `caPref : Fin 6 → Bool`, tabulated over the six transitive
strict orderings of `{a, b, c}` (`false` = prefers `c`, `true` = prefers `a`):

| `k` | ordering | `caPref k` | sign |
|---|---|---|---|
| 0 | a>b>c | `true`  | `-1` |
| 1 | a>c>b | `true`  | `-1` |
| 2 | b>a>c | `true`  | `-1` |
| 3 | b>c>a | `false` | `+1` |
| 4 | c>a>b | `false` | `+1` |
| 5 | c>b>a | `false` | `+1` |

The comparison is oriented `c` versus `a`, so the "first alternative" is `c`:
`boolToSign` sends `false ↦ +1` = "pro `c`" and `true ↦ -1` = "pro `a`".
Definition by pattern match on `Fin 6` literals; no proof.

**Remark.** Two features distinguish this table from `abPref` and `bcPref`.

- Its blocks are contiguous — orderings 0, 1, 2 rank `a` above `c`, orderings
  3, 4, 5 rank `c` above `a` — because the `Fin 6` indexing happens to sort the
  orderings that way.
- Its orientation is *reversed* relative to the other two, which is what makes
  the cycle well posed: for a transitive ordering the three signs are never all
  `+1` nor all `-1`. Ordering 0 (`a>b>c`) gives `(+1, +1, -1)`, not
  `(+1, +1, +1)` — a single voter never exhibits a Condorcet cycle, so a cycle
  in society's output must come from `f`, which is precisely what `acyclic`
  forbids.

**Used in.** `caVotes`, plus the finite computations `sum_caPref_sign`,
`sum_bcPref_caPref`, `sum_abPref_caPref`.
