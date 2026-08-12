<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/ArrowTheorem.lean :: bcPref -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# The b-vs-c ballot of each of the six orderings

**Definition.** `bcPref : Fin 6 → Bool`, tabulated over the six transitive
strict orderings of `{a, b, c}` (`false` = prefers `b`):

| `k` | ordering | `bcPref k` | sign |
|---|---|---|---|
| 0 | a>b>c | `false` | `+1` |
| 1 | a>c>b | `true`  | `-1` |
| 2 | b>a>c | `false` | `+1` |
| 3 | b>c>a | `false` | `+1` |
| 4 | c>a>b | `true`  | `-1` |
| 5 | c>b>a | `true`  | `-1` |

The sign column is `boolToSign (bcPref k)` (`false ↦ 1`, `true ↦ -1`), so `+1`
means "pro `b`". The entry only reads off the relative order of `b` and `c`,
ignoring where `a` sits: orderings 0, 2, 3 all put `b` above `c`. Definition by
pattern match on `Fin 6` literals; no proof.

**Remark.** The middle comparison of the cycle `a > b > c > a`. Three orderings
favour `b` and three favour `c` — the content of `sum_bcPref_sign` — and pairing
this table against `abPref` or `caPref` gives the cross-sum `-2`
(`sum_abPref_bcPref`, `sum_bcPref_caPref`), i.e. correlation `-1/3` between any
two of a voter's three pairwise ballots.

**Used in.** `bcVotes`, plus the finite computations `sum_bcPref_sign`,
`sum_abPref_bcPref`, `sum_bcPref_caPref`.
