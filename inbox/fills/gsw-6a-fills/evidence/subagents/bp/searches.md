# bp (U4) duplication / name searches

| # | Query | Tool | Result |
|---|---|---|---|
| S1 | `maxDepth_le\|maxFaninL_le\|maxDepth_map\|maxFaninL_map\|le_maxDepth` over TCSlib | grep | only Basic `depth_le_maxDepth` (member <= max), `maxFaninL_le_sumSize`; private `TreeDAG.lean:407,420` (`maxDepth_map`,`maxFaninL_map`), private `TreeNCAC.lean:215,226` (`maxDepth_map_le`,`maxFaninL_map_le`); no public converse. Use lead's Addendum A family `maxDepth_le_of_forall`, `maxFaninL_le_of_forall`. |
| S2 | public `theorem .*(maxDepth|maxFaninL)` over TCSlib, audits | grep | Basic nil/cons/depth_le_maxDepth/maxFanin_le_maxFaninL/maxFaninL_le_sumSize; CarrySave `maxFaninL_csaStep_le` etc. (unrelated) |
| S3 | `node true [])\.eval`, `node false [])\.eval`, `node _ []` | grep TCSlib | none (only `const_eval` in Combinators for `const b`, a different def) |
| S4 | Nat.clog lemmas | grep Mathlib/Data/Nat/Log.lean | `clog_of_two_le` (n+b-1)/b form, `clog_le_iff_le_pow`, `le_pow_clog`, `clog_mono_right`, `clog_of_right_le_one`; NO `clog_le_of_le_pow` (use `clog_le_iff_le_pow`) |
| S5 | new helper names `maxDepth_le_of_forall maxFaninL_le_of_forall maxFanin_wireComp_le compTree_eval_aux eval_node_true_nil eval_node_false_nil yield_singleton yield_mk_append` | grep TCSlib audits | none exist |
