| target | source (both in `TwoTapes`) | share | disposition |
|---|---|---|---|
| `tt_D_inv` | `tt_D_succ` | 109/123 = 89% | the `show (match …) = _; rw [hq]` idiom reading this file's own `match` definitions (`tt_D`, `tt_T`, `tt_idxR`) at a live state |
| `tt_D` | `tt_idxR` | 84/97 = 87% | term pair: `tt_D`, `tt_T`, `tt_idxR` share their `match (tt_c M x r).state with` head |
| `tt_cs_round` | `tt_cs_halt` | 547/632 = 87% | `tt_cs_round` and `tt_cs_halt` open alike (the round's start `tt_cs_start` and action `tt_round_inv`) and then use `tt_round`'s two clauses |
| `tt_rsum_rebalance_false` | `tt_rsum_rebalance_true` | 1258/1498 = 84% | left/right mirror pair (the right and the left move read different library lemmas — `words true`/`false`, `zoneCascadeRight_lengths`/`Left_lengths` — with opposite signs; the library's own mirror `zoneRebalance_false` does not carry fullness, so each direction is proved) |
| `tt_T` | `tt_idxR` | 81/97 = 84% | term pair: `tt_D`, `tt_T`, `tt_idxR` share their `match (tt_c M x r).state with` head |
| `tt_full_pre_false` | `tt_full_pre_true` | 525/629 = 83% | left/right mirror pair (the right and the left move read different library lemmas — `words true`/`false`, `zoneCascadeRight_lengths`/`Left_lengths` — with opposite signs; the library's own mirror `zoneRebalance_false` does not carry fullness, so each direction is proved) |
| `tt_full_pre_true` | `tt_full_pre_false` | 525/636 = 83% | left/right mirror pair (the right and the left move read different library lemmas — `words true`/`false`, `zoneCascadeRight_lengths`/`Left_lengths` — with opposite signs; the library's own mirror `zoneRebalance_false` does not carry fullness, so each direction is proved) |
| `tt_full_rebalance_true` | `tt_full_rebalance_false` | 1323/1649 = 80% | left/right mirror pair (the right and the left move read different library lemmas — `words true`/`false`, `zoneCascadeRight_lengths`/`Left_lengths` — with opposite signs; the library's own mirror `zoneRebalance_false` does not carry fullness, so each direction is proved) |
| `tt_rsum_rebalance_true` | `tt_rsum_rebalance_false` | 1258/1596 = 79% | left/right mirror pair (the right and the left move read different library lemmas — `words true`/`false`, `zoneCascadeRight_lengths`/`Left_lengths` — with opposite signs; the library's own mirror `zoneRebalance_false` does not carry fullness, so each direction is proved) |
| `tt_full_rebalance_false` | `tt_full_rebalance_true` | 1323/1705 = 78% | left/right mirror pair (the right and the left move read different library lemmas — `words true`/`false`, `zoneCascadeRight_lengths`/`Left_lengths` — with opposite signs; the library's own mirror `zoneRebalance_false` does not carry fullness, so each direction is proved) |
| `tt_orbit_rsum` | `tt_T_ge` | 90/125 = 72% | the same `match`-reading idiom |
| `tt_orbit_rsum` | `tt_D_succ` | 88/123 = 72% | the `show (match …) = _; rw [hq]` idiom reading this file's own `match` definitions (`tt_D`, `tt_T`, `tt_idxR`) at a live state |
| `tt_D_level` | `tt_D_succ` | 88/123 = 72% | the `show (match …) = _; rw [hq]` idiom reading this file's own `match` definitions (`tt_D`, `tt_T`, `tt_idxR`) at a live state |
| `tt_cs_round` | `tt_T_ge` | 87/125 = 70% | the same `match`-reading idiom |
| `tt_Dtr_level_mono` | `tt_Dtr_other` | 383/582 = 66% | two inductions over a round's tracks with `tt_Dtr`'s case split |
| `tt_cs_round` | `tt_D_succ` | 77/123 = 63% | the `show (match …) = _; rw [hq]` idiom reading this file's own `match` definitions (`tt_D`, `tt_T`, `tt_idxR`) at a live state |
| `tt_Dtr_other` | `tt_Dtr_level_mono` | 383/639 = 60% | two inductions over a round's tracks with `tt_Dtr`'s case split |
| `tt_full_rebalance_true` | `tt_full_pre_true` | 375/629 = 60% | `tt_full_rebalance_*` re-derive the classical pre-state that `tt_full_pre_*` package (written first; a refactor would let them cite `tt_full_pre_*`) |
| `tt_full_rebalance_false` | `tt_full_pre_false` | 379/636 = 60% | `tt_full_rebalance_*` re-derive the classical pre-state that `tt_full_pre_*` package (written first; a refactor would let them cite `tt_full_pre_*`) |
| `tt_T` | `tt_D` | 85/146 = 58% | term pair: `tt_D`, `tt_T`, `tt_idxR` share their `match (tt_c M x r).state with` head |
| `tt_cost` | `tt_T_ge` | 72/125 = 58% | the same `match`-reading idiom |
| `tt_idxR` | `tt_D` | 84/146 = 58% | term pair: `tt_D`, `tt_T`, `tt_idxR` share their `match (tt_c M x r).state with` head |
| `tt_cs_round` | `tt_orbit_rsum` | 141/248 = 57% | the round's start and action, read alike |
| `tt_D_level` | `tt_D_inv` | 381/713 = 53% | the orbit's inductions share the halted/live case split |
