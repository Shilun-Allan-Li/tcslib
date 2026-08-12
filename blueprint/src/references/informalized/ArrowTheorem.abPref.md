<!-- generated-by: proofmatch informalization (uncited) -->
<!-- lean-source: TCSlib/BooleanAnalysis/ArrowTheorem.lean :: abPref -->
<!-- origin: no source citation; informalized directly from the Lean proof -->

# The a-vs-b ballot of each of the six orderings

**Definition.** `abPref : Fin 6 → Bool`, given by a table on the six transitive
strict orderings of `{a, b, c}` (`false` = prefers `a`):

| `k` | ordering | `abPref k` | sign |
|---|---|---|---|
| 0 | a>b>c | `false` | `+1` |
| 1 | a>c>b | `false` | `+1` |
| 2 | b>a>c | `true`  | `-1` |
| 3 | b>c>a | `true`  | `-1` |
| 4 | c>a>b | `false` | `+1` |
| 5 | c>b>a | `true`  | `-1` |

The sign column is `boolToSign (abPref k)`, i.e. `false ↦ 1`, `true ↦ -1`
("pro first alternative" ↦ `+1`). Ordering 4 (`c>a>b`) is the one worth
checking: `c` wins overall, but `a` still beats `b`, so the a-vs-b ballot is
`false`. Definition by pattern match on `Fin 6` literals; no proof.

**Remark.** Three orderings rank `a` above `b` and three rank `b` above `a`,
which is exactly the balance recorded by `sum_abPref_sign`. Together with its
siblings `bcPref` and `caPref` this fixes the encoding of one voter as a triple
of pairwise ±1 ballots; all downstream arithmetic (`sum_abPref_bcPref = -2`,
giving per-voter correlation `-2/6 = -1/3`) is just `Fin.sum_univ_six` plus
`norm_num` over these tables.

**Used in.** `abVotes` (lifting the table along a profile), and the three
finite computations `sum_abPref_sign`, `sum_abPref_bcPref`,
`sum_abPref_caPref`.
