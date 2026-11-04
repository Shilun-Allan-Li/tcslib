| identifier | resolves to | kind | module | tactics | uses | first line | class |
|---|---|---|---|---|---|---|---|
| `Or.inl` | `Or.inl` | ctor | Init.Prelude | rw | 1 | 1046 | Core/Mathlib: ctor |
| `Or.inr` | `Or.inr` | ctor | Init.Prelude | rw | 1 | 1042 | Core/Mathlib: ctor |
| `Sum.inl` | `Sum.inl` | ctor | Init.Core | show | 3 | 5014 | Core/Mathlib: ctor |
| `none` | `Option.none` | ctor | Init.Prelude | rw,show | 17 | 1119 | Core/Mathlib: ctor |
| `some` | `Option.some` | ctor | Init.Prelude | rw | 7 | 976 | Core/Mathlib: ctor |
| `Fin.last` | `Fin.last` | def | Init.Data.Fin.Basic | show | 2 | 1799 | Core/Mathlib: definition in show/change (reduces in a show step: allowed) |
| `Nat.bits` | `Nat.bits` | def | Mathlib.Data.Nat.Bits | show | 1 | 3046 | Core/Mathlib: definition in show/change (reduces in a show step: allowed) |
| `Function.update` | `Function.update` | def | Mathlib.Logic.Function.Basic | rw,show | 5 | 1340 | Core/Mathlib: definition named in `show` goals and in the type of a `have` nested in a `rw` list; never a rewrite rule or unfolded (reviewed) |
| `Bool` | `Bool` | inductive | Init.Prelude | rw,show | 3 | 976 | Core/Mathlib: inductive |
| `Option` | `Option` | inductive | Init.Prelude | show | 3 | 984 | Core/Mathlib: inductive |
| `Bool.false_ne_true` | `Bool.false_ne_true` | theorem | Init.Data.Bool | rw | 2 | 4773 | Core/Mathlib: theorem |
| `Bool.toNat_false` | `Bool.toNat_false` | theorem | Init.Data.Bool | rw | 1 | 407 | Core/Mathlib: theorem |
| `Bool.toNat_true` | `Bool.toNat_true` | theorem | Init.Data.Bool | rw | 2 | 397 | Core/Mathlib: theorem |
| `Fin.coe_castSucc` | `Fin.coe_castSucc` | theorem | Init.Data.Fin.Lemmas | rw | 2 | 3292 | Core/Mathlib: theorem |
| `Fin.lastCases_castSucc` | `Fin.lastCases_castSucc` | theorem | Init.Data.Fin.Lemmas | rw | 8 | 1726 | Core/Mathlib: theorem |
| `Fin.lastCases_last` | `Fin.lastCases_last` | theorem | Init.Data.Fin.Lemmas | rw | 8 | 1724 | Core/Mathlib: theorem |
| `Fin.val_last` | `Fin.val_last` | theorem | Init.Data.Fin.Lemmas | rw | 2 | 3299 | Core/Mathlib: theorem |
| `Finset.sum_range_succ` | `Finset.sum_range_succ` | theorem | Mathlib.Algebra.BigOperators.Group.Finset.Basic | rw | 3 | 387 | Core/Mathlib: theorem |
| `Function.Embedding.coeFn_mk` | `Function.Embedding.coeFn_mk` | theorem | Mathlib.Logic.Embedding.Basic | rw,simp only | 5 | 2438 | Core/Mathlib: theorem |
| `Function.Embedding.coe_refl` | `Function.Embedding.coe_refl` | theorem | Mathlib.Logic.Embedding.Basic | rw | 1 | 1622 | Core/Mathlib: theorem |
| `Function.update_eq_self` | `Function.update_eq_self` | theorem | Mathlib.Logic.Function.Basic | rw | 2 | 985 | Core/Mathlib: theorem |
| `Function.update_idem` | `Function.update_idem` | theorem | Mathlib.Logic.Function.Basic | rw | 6 | 1362 | Core/Mathlib: theorem |
| `Function.update_of_ne` | `Function.update_of_ne` | theorem | Mathlib.Logic.Function.Basic | rw,simp | 63 | 668 | Core/Mathlib: theorem |
| `Function.update_self` | `Function.update_self` | theorem | Mathlib.Logic.Function.Basic | rw | 31 | 662 | Core/Mathlib: theorem |
| `List.append_assoc` | `List.append_assoc` | theorem | Init.Data.List.Basic | rw | 5 | 1287 | Core/Mathlib: theorem |
| `List.append_nil` | `List.append_nil` | theorem | Init.Data.List.Basic | rw | 21 | 950 | Core/Mathlib: theorem |
| `List.cons_append` | `List.cons_append` | theorem | Init.Data.List.Basic | rw | 1 | 407 | Core/Mathlib: theorem |
| `List.drop_drop` | `List.drop_drop` | theorem | Init.Data.List.TakeDrop | rw | 2 | 1357 | Core/Mathlib: theorem |
| `List.flatMap_append` | `List.flatMap_append` | theorem | Init.Data.List.Basic | rw | 3 | 4754 | Core/Mathlib: theorem |
| `List.flatMap_cons` | `List.flatMap_cons` | theorem | Init.Data.List.Basic | rw | 4 | 1425 | Core/Mathlib: theorem |
| `List.flatten_replicate_singleton` | `List.flatten_replicate_singleton` | theorem | Init.Data.List.Lemmas | rw | 1 | 1999 | Core/Mathlib: theorem |
| `List.getElem?_append_left` | `List.getElem?_append_left` | theorem | Init.Data.List.Lemmas | rw | 1 | 618 | Core/Mathlib: theorem |
| `List.getElem?_eq_getElem` | `List.getElem?_eq_getElem` | theorem | Init.GetElem | rw | 7 | 1096 | Core/Mathlib: theorem |
| `List.getElem?_eq_none` | `List.getElem?_eq_none` | theorem | Init.GetElem | rw | 6 | 1116 | Core/Mathlib: theorem |
| `List.getElem?_map` | `List.getElem?_map` | theorem | Init.Data.List.Lemmas | rw | 1 | 628 | Core/Mathlib: theorem |
| `List.getElem?_replicate_of_lt` | `List.getElem?_replicate_of_lt` | theorem | Init.Data.List.Lemmas | rw | 1 | 1988 | Core/Mathlib: theorem |
| `List.head?_drop` | `List.head?_drop` | theorem | Init.Data.List.Nat.TakeDrop | rw | 2 | 1354 | Core/Mathlib: theorem |
| `List.head?_eq_none_iff` | `List.head?_eq_none_iff` | theorem | Init.Data.List.Lemmas | rw | 1 | 1394 | Core/Mathlib: theorem |
| `List.length_append` | `List.length_append` | theorem | Init.Data.List.Basic | rw,simp only | 6 | 620 | Core/Mathlib: theorem |
| `List.length_cons` | `List.length_cons` | theorem | Init.Data.List.Basic | rw,simp only | 12 | 1370 | Core/Mathlib: theorem |
| `List.length_drop` | `List.length_drop` | theorem | Init.Data.List.TakeDrop | rw | 3 | 1336 | Core/Mathlib: theorem |
| `List.length_map` | `List.length_map` | theorem | Init.Data.List.Lemmas | rw | 5 | 664 | Core/Mathlib: theorem |
| `List.length_nil` | `List.length_nil` | theorem | Init.Data.List.Basic | rw,simp only | 15 | 1336 | Core/Mathlib: theorem |
| `List.length_replicate` | `List.length_replicate` | theorem | Init.Data.List.Basic | rw,simp only | 39 | 1628 | Core/Mathlib: theorem |
| `List.length_singleton` | `List.length_singleton` | theorem | Init.Data.List.Basic | rw | 3 | 1999 | Core/Mathlib: theorem |
| `List.map_cons` | `List.map_cons` | theorem | Init.Data.List.Basic | rw | 3 | 397 | Core/Mathlib: theorem |
| `List.map_id` | `List.map_id` | theorem | Init.Data.List.Lemmas | rw | 1 | 1622 | Core/Mathlib: theorem |
| `List.map_id'` | `List.map_id'` | theorem | Init.Data.List.Lemmas | rw | 5 | 3430 | Core/Mathlib: theorem |
| `List.map_nil` | `List.map_nil` | theorem | Init.Data.List.Basic | rw | 1 | 2057 | Core/Mathlib: theorem |
| `List.map_replicate` | `List.map_replicate` | theorem | Init.Data.List.Lemmas | rw | 1 | 3769 | Core/Mathlib: theorem |
| `List.nil_append` | `List.nil_append` | theorem | Init.Data.List.Basic | rw | 6 | 3430 | Core/Mathlib: theorem |
| `List.replicate_append_replicate` | `List.replicate_append_replicate` | theorem | Init.Data.List.Lemmas | rw | 2 | 3138 | Core/Mathlib: theorem |
| `List.replicate_succ` | `List.replicate_succ` | theorem | Init.Data.List.Basic | rw | 2 | 397 | Core/Mathlib: theorem |
| `List.replicate_succ'` | `List.replicate_succ'` | theorem | Init.Data.List.Lemmas | rw,simp | 8 | 1309 | Core/Mathlib: theorem |
| `List.replicate_zero` | `List.replicate_zero` | theorem | Init.Data.List.Basic | rw | 1 | 1306 | Core/Mathlib: theorem |
| `List.take_length` | `List.take_length` | theorem | Init.Data.List.TakeDrop | rw | 2 | 1295 | Core/Mathlib: theorem |
| `List.take_succ` | `List.take_succ` | theorem | Init.Data.List.TakeDrop | rw | 2 | 1287 | Core/Mathlib: theorem |
| `List.take_zero` | `List.take_zero` | theorem | Init.Data.List.Basic | rw | 2 | 1284 | Core/Mathlib: theorem |
| `Nat.add_assoc` | `Nat.add_assoc` | theorem | Init.Data.Nat.Basic | rw | 1 | 1151 | Core/Mathlib: theorem |
| `Nat.add_zero` | `Nat.add_zero` | theorem | Init.Core | rw | 1 | 1148 | Core/Mathlib: theorem |
| `Nat.cast_zero` | `Nat.cast_zero` | theorem | Mathlib.Data.Nat.Cast.Defs | rw | 3 | 1091 | Core/Mathlib: theorem |
| `Nat.ofDigits_cons` | `Nat.ofDigits_cons` | theorem | Mathlib.Data.Nat.Digits.Defs | rw | 2 | 397 | Core/Mathlib: theorem |
| `Nat.ofDigits_singleton` | `Nat.ofDigits_singleton` | theorem | Mathlib.Data.Nat.Digits.Defs | rw | 1 | 2057 | Core/Mathlib: theorem |
| `Nat.size_eq_bits_len` | `Nat.size_eq_bits_len` | theorem | Mathlib.Data.Nat.Size | rw | 5 | 415 | Core/Mathlib: theorem |
| `Nat.succ_pos` | `Nat.succ_pos` | theorem | Init.Prelude | rw | 1 | 3271 | Core/Mathlib: theorem |
| `Nat.unpair_pair` | `Nat.unpair_pair` | theorem | Mathlib.Data.Nat.Pairing | rw | 4 | 3250 | Core/Mathlib: theorem |
| `Nat.unpair_zero` | `Nat.unpair_zero` | theorem | Mathlib.Data.Nat.Pairing | rw | 1 | 5128 | Core/Mathlib: theorem |
| `Nat.zero_bits` | `Nat.zero_bits` | theorem | Mathlib.Data.Nat.Bits | rw | 3 | 3227 | Core/Mathlib: theorem |
| `Option.getD_none` | `Option.getD_none` | theorem | Init.Data.Option.Basic | rw | 1 | 985 | Core/Mathlib: theorem |
| `Option.map_some` | `Option.map_some` | theorem | Init.Data.Option.Basic | rw | 2 | 542 | Core/Mathlib: theorem |
| `Option.some.inj` | `Option.some.inj` | theorem | Init.Core | rw | 2 | 3342 | Core/Mathlib: theorem |
| `Option.some.injEq` | `Option.some.injEq` | theorem | Init.Core | simp only | 3 | 3089 | Core/Mathlib: theorem |
| `Option.toList_none` | `Option.toList_none` | theorem | Init.Data.Option.Lemmas | rw | 13 | 1103 | Core/Mathlib: theorem |
| `Option.toList_some` | `Option.toList_some` | theorem | Init.Data.Option.Lemmas | rw | 4 | 1287 | Core/Mathlib: theorem |
| `Set.mem_insert_iff` | `Set.mem_insert_iff` | theorem | Mathlib.Data.Set.Insert | simp only | 3 | 3089 | Core/Mathlib: theorem |
| `Set.mem_singleton_iff` | `Set.mem_singleton_iff` | theorem | Mathlib.Data.Set.Insert | simp only | 3 | 3089 | Core/Mathlib: theorem |
| `Sigma.mk.inj_iff` | `Sigma.mk.inj_iff` | theorem | Mathlib.Data.Sigma.Basic | simp only | 3 | 3089 | Core/Mathlib: theorem |
| `SignType.coe_zero` | `SignType.coe_zero` | theorem | Mathlib.Data.Sign.Defs | rw | 3 | 1047 | Core/Mathlib: theorem |
| `add_mul` | `add_mul` | theorem | Mathlib.Algebra.Ring.Defs | rw | 1 | 4279 | Core/Mathlib: theorem |
| `add_zero` | `add_zero` | theorem | Mathlib.Algebra.Group.Defs | rw | 3 | 1047 | Core/Mathlib: theorem |
| `compare_eq_iff_eq` | `compare_eq_iff_eq` | theorem | Mathlib.Order.Defs.LinearOrder | rw | 1 | 1128 | Core/Mathlib: theorem |
| `compare_gt_iff_gt` | `compare_gt_iff_gt` | theorem | Mathlib.Order.Defs.LinearOrder | rw | 2 | 1137 | Core/Mathlib: theorem |
| `compare_lt_iff_lt` | `compare_lt_iff_lt` | theorem | Mathlib.Order.Defs.LinearOrder | rw | 1 | 1119 | Core/Mathlib: theorem |
| `dif_neg` | `dif_neg` | theorem | Init.Core | rw | 11 | 1295 | Core/Mathlib: theorem |
| `dif_pos` | `dif_pos` | theorem | Init.Core | rw | 13 | 1287 | Core/Mathlib: theorem |
| `em` | `em` | theorem | Mathlib.Logic.Basic | rw | 2 | 1309 | Core/Mathlib: theorem |
| `false_and` | `false_and` | theorem | Init.SimpLemmas | simp only | 3 | 3089 | Core/Mathlib: theorem |
| `false_or` | `false_or` | theorem | Init.SimpLemmas | simp only | 2 | 3089 | Core/Mathlib: theorem |
| `heq_eq_eq` | `heq_eq_eq` | theorem | Init.SimpLemmas | simp only | 3 | 3089 | Core/Mathlib: theorem |
| `if_neg` | `if_neg` | theorem | Init.Core | rw,simp only | 47 | 616 | Core/Mathlib: theorem |
| `if_pos` | `if_pos` | theorem | Init.Core | rw | 32 | 611 | Core/Mathlib: theorem |
| `if_true` | `if_true` | theorem | Init.ByCases | simp only | 1 | 1423 | Core/Mathlib: theorem |
| `le_rfl` | `le_rfl` | theorem | Mathlib.Order.Defs.PartialOrder | rw | 8 | 1109 | Core/Mathlib: theorem |
| `lt_irrefl` | `lt_irrefl` | theorem | Mathlib.Order.Defs.PartialOrder | rw | 2 | 3271 | Core/Mathlib: theorem |
| `mul_assoc` | `mul_assoc` | theorem | Mathlib.Algebra.Group.Defs | rw | 8 | 2319 | Core/Mathlib: theorem |
| `mul_comm` | `mul_comm` | theorem | Mathlib.Algebra.Group.Defs | rw,simp | 3 | 4299 | Core/Mathlib: theorem |
| `mul_one` | `mul_one` | theorem | Mathlib.Algebra.Group.Defs | rw | 2 | 1999 | Core/Mathlib: theorem |
| `mul_pow` | `mul_pow` | theorem | Mathlib.Algebra.Group.Basic | rw | 1 | 4299 | Core/Mathlib: theorem |
| `one_mul` | `one_mul` | theorem | Mathlib.Algebra.Group.Defs | rw | 2 | 2289 | Core/Mathlib: theorem |
| `or_false` | `or_false` | theorem | Init.SimpLemmas | simp only | 1 | 3146 | Core/Mathlib: theorem |
| `pow_add` | `pow_add` | theorem | Mathlib.Algebra.Group.Defs | rw | 2 | 415 | Core/Mathlib: theorem |
| `pow_mul` | `pow_mul` | theorem | Mathlib.Algebra.Group.Defs | rw | 2 | 379 | Core/Mathlib: theorem |
| `pow_succ` | `pow_succ` | theorem | Mathlib.Algebra.Group.Defs | rw | 5 | 397 | Core/Mathlib: theorem |
| `sub_eq_add_neg` | `sub_eq_add_neg` | theorem | Mathlib.Algebra.Group.Defs | rw | 1 | 1112 | Core/Mathlib: theorem |
| `sub_self` | `sub_self` | theorem | Mathlib.Algebra.Group.Defs | rw | 2 | 806 | Core/Mathlib: theorem |
| `sub_zero` | `sub_zero` | theorem | Mathlib.Algebra.Group.Basic | rw | 3 | 694 | Core/Mathlib: theorem |
| `symm` | `symm` | theorem | Mathlib.Order.Defs.Unbundled | rw | 1 | 727 | Core/Mathlib: theorem |
| `true_and` | `true_and` | theorem | Init.SimpLemmas | simp only | 4 | 2000 | Core/Mathlib: theorem |
| `zero_add` | `zero_add` | theorem | Mathlib.Algebra.Group.Defs | rw | 9 | 655 | Core/Mathlib: theorem |
| `zero_mul` | `MulZeroClass.zero_mul` | theorem (projection) | Mathlib.Algebra.GroupWithZero.Defs | simp only | 1 | 5236 | Core/Mathlib: theorem |
| `reduceCtorEq` | `reduceCtorEq` | def | Lean.Meta.Tactic.Simp.BuiltinSimprocs.Core | simp only | 3 | 3089 | Core: simproc (constructor disequality), run by simp, not a definition unfolded |
| `C.k` | `-` | (unresolved: a local, a field or a binder) | - | show | 2 | 1799 | local (hypothesis, binder or field) |
| `C.tm` | `-` | (unresolved: a local, a field or a binder) | - | rw | 5 | 909 | local (hypothesis, binder or field) |
| `H` | `-` | (unresolved: a local, a field or a binder) | - | rw | 5 | 4098 | local (hypothesis, binder or field) |
| `K` | `-` | (unresolved: a local, a field or a binder) | - | rw | 8 | 976 | local (hypothesis, binder or field) |
| `M` | `-` | (unresolved: a local, a field or a binder) | - | rw | 10 | 1287 | local (hypothesis, binder or field) |
| `P` | `-` | (unresolved: a local, a field or a binder) | - | rw,show | 25 | 976 | local (hypothesis, binder or field) |
| `P'` | `-` | (unresolved: a local, a field or a binder) | - | show | 2 | 2006 | local (hypothesis, binder or field) |
| `Q` | `-` | (unresolved: a local, a field or a binder) | - | rw | 6 | 1309 | local (hypothesis, binder or field) |
| `S` | `-` | (unresolved: a local, a field or a binder) | - | rw | 1 | 976 | local (hypothesis, binder or field) |
| `T` | `-` | (unresolved: a local, a field or a binder) | - | rw,show | 31 | 976 | local (hypothesis, binder or field) |
| `T'` | `-` | (unresolved: a local, a field or a binder) | - | show | 4 | 1799 | local (hypothesis, binder or field) |
| `a` | `-` | (unresolved: a local, a field or a binder) | - | rw,show | 21 | 1103 | local (hypothesis, binder or field) |
| `b` | `-` | (unresolved: a local, a field or a binder) | - | rw | 26 | 1103 | local (hypothesis, binder or field) |
| `c6` | `-` | (unresolved: a local, a field or a binder) | - | rw | 1 | 3096 | local (hypothesis, binder or field) |
| `c6o` | `-` | (unresolved: a local, a field or a binder) | - | rw | 2 | 4916 | local (hypothesis, binder or field) |
| `cq` | `-` | (unresolved: a local, a field or a binder) | - | show | 1 | 2359 | local (hypothesis, binder or field) |
| `cu` | `-` | (unresolved: a local, a field or a binder) | - | show | 1 | 2327 | local (hypothesis, binder or field) |
| `d` | `-` | (unresolved: a local, a field or a binder) | - | rw,show | 4 | 1976 | local (hypothesis, binder or field) |
| `dl` | `-` | (unresolved: a local, a field or a binder) | - | rw | 1 | 1394 | local (hypothesis, binder or field) |
| `done` | `-` | (unresolved: a local, a field or a binder) | - | rw | 2 | 1466 | local (hypothesis, binder or field) |
| `e` | `-` | (unresolved: a local, a field or a binder) | - | rw | 11 | 3250 | local (hypothesis, binder or field) |
| `e1` | `-` | (unresolved: a local, a field or a binder) | - | rw | 2 | 3500 | local (hypothesis, binder or field) |
| `e10` | `-` | (unresolved: a local, a field or a binder) | - | rw,simp | 5 | 4016 | local (hypothesis, binder or field) |
| `e11` | `-` | (unresolved: a local, a field or a binder) | - | rw,simp | 5 | 4016 | local (hypothesis, binder or field) |
| `e2` | `-` | (unresolved: a local, a field or a binder) | - | rw | 1 | 3500 | local (hypothesis, binder or field) |
| `e5` | `-` | (unresolved: a local, a field or a binder) | - | rw | 2 | 5077 | local (hypothesis, binder or field) |
| `e6` | `-` | (unresolved: a local, a field or a binder) | - | rw | 1 | 4349 | local (hypothesis, binder or field) |
| `e7` | `-` | (unresolved: a local, a field or a binder) | - | rw | 1 | 4382 | local (hypothesis, binder or field) |
| `e8` | `-` | (unresolved: a local, a field or a binder) | - | rw | 1 | 4382 | local (hypothesis, binder or field) |
| `entry` | `-` | (unresolved: a local, a field or a binder) | - | rw | 6 | 909 | local (hypothesis, binder or field) |
| `eq` | `-` | (unresolved: a local, a field or a binder) | - | rw | 1 | 1128 | local (hypothesis, binder or field) |
| `exact` | `-` | (unresolved: a local, a field or a binder) | - | rw | 3 | 1394 | local (hypothesis, binder or field) |
| `f` | `-` | (unresolved: a local, a field or a binder) | - | rw | 3 | 5170 | local (hypothesis, binder or field) |
| `g` | `-` | (unresolved: a local, a field or a binder) | - | rw | 3 | 5170 | local (hypothesis, binder or field) |
| `getD` | `-` | (unresolved: a local, a field or a binder) | - | show | 1 | 984 | local (hypothesis, binder or field) |
| `got` | `-` | (unresolved: a local, a field or a binder) | - | rw | 1 | 1362 | local (hypothesis, binder or field) |
| `gt` | `-` | (unresolved: a local, a field or a binder) | - | rw | 1 | 1137 | local (hypothesis, binder or field) |
| `h` | `-` | (unresolved: a local, a field or a binder) | - | rw,simp | 57 | 537 | local (hypothesis, binder or field) |
| `h0` | `-` | (unresolved: a local, a field or a binder) | - | rw | 7 | 1648 | local (hypothesis, binder or field) |
| `h1` | `-` | (unresolved: a local, a field or a binder) | - | rw,simp | 11 | 1176 | local (hypothesis, binder or field) |
| `h10` | `-` | (unresolved: a local, a field or a binder) | - | rw | 1 | 4010 | local (hypothesis, binder or field) |
| `h11` | `-` | (unresolved: a local, a field or a binder) | - | rw | 1 | 4014 | local (hypothesis, binder or field) |
| `h2` | `-` | (unresolved: a local, a field or a binder) | - | rw,simp | 9 | 1394 | local (hypothesis, binder or field) |
| `h3` | `-` | (unresolved: a local, a field or a binder) | - | rw,simp | 5 | 3847 | local (hypothesis, binder or field) |
| `h4` | `-` | (unresolved: a local, a field or a binder) | - | simp | 2 | 3675 | local (hypothesis, binder or field) |
| `h5` | `-` | (unresolved: a local, a field or a binder) | - | rw,simp | 3 | 3737 | local (hypothesis, binder or field) |
| `h6` | `-` | (unresolved: a local, a field or a binder) | - | rw,simp | 6 | 3847 | local (hypothesis, binder or field) |
| `h7` | `-` | (unresolved: a local, a field or a binder) | - | rw,simp | 4 | 3500 | local (hypothesis, binder or field) |
| `h8` | `-` | (unresolved: a local, a field or a binder) | - | simp | 2 | 3605 | local (hypothesis, binder or field) |
| `hA` | `-` | (unresolved: a local, a field or a binder) | - | rw | 5 | 4500 | local (hypothesis, binder or field) |
| `hD` | `-` | (unresolved: a local, a field or a binder) | - | rw | 1 | 822 | local (hypothesis, binder or field) |
| `hE'` | `-` | (unresolved: a local, a field or a binder) | - | rw | 3 | 1885 | local (hypothesis, binder or field) |
| `hJ` | `-` | (unresolved: a local, a field or a binder) | - | simp | 1 | 4182 | local (hypothesis, binder or field) |
| `hK` | `-` | (unresolved: a local, a field or a binder) | - | simp | 3 | 4099 | local (hypothesis, binder or field) |
| `hLb` | `-` | (unresolved: a local, a field or a binder) | - | simp | 3 | 3589 | local (hypothesis, binder or field) |
| `hM` | `-` | (unresolved: a local, a field or a binder) | - | rw,simp only | 20 | 1287 | local (hypothesis, binder or field) |
| `hN` | `-` | (unresolved: a local, a field or a binder) | - | rw | 1 | 4773 | local (hypothesis, binder or field) |
| `hP` | `-` | (unresolved: a local, a field or a binder) | - | rw | 7 | 755 | local (hypothesis, binder or field) |
| `hP'` | `-` | (unresolved: a local, a field or a binder) | - | rw | 6 | 947 | local (hypothesis, binder or field) |
| `hP0` | `-` | (unresolved: a local, a field or a binder) | - | rw | 3 | 1091 | local (hypothesis, binder or field) |
| `hP13` | `-` | (unresolved: a local, a field or a binder) | - | rw,simp | 3 | 3813 | local (hypothesis, binder or field) |
| `hP15` | `-` | (unresolved: a local, a field or a binder) | - | rw | 1 | 3826 | local (hypothesis, binder or field) |
| `hP2` | `-` | (unresolved: a local, a field or a binder) | - | rw,simp | 3 | 3015 | local (hypothesis, binder or field) |
| `hP4` | `-` | (unresolved: a local, a field or a binder) | - | rw,simp | 5 | 3028 | local (hypothesis, binder or field) |
| `hP6` | `-` | (unresolved: a local, a field or a binder) | - | rw | 1 | 3656 | local (hypothesis, binder or field) |
| `hPa` | `-` | (unresolved: a local, a field or a binder) | - | rw | 1 | 1076 | local (hypothesis, binder or field) |
| `hPb` | `-` | (unresolved: a local, a field or a binder) | - | rw | 1 | 1073 | local (hypothesis, binder or field) |
| `hPc` | `-` | (unresolved: a local, a field or a binder) | - | rw,show | 5 | 1731 | local (hypothesis, binder or field) |
| `hPd` | `-` | (unresolved: a local, a field or a binder) | - | rw | 2 | 694 | local (hypothesis, binder or field) |
| `hPs` | `-` | (unresolved: a local, a field or a binder) | - | rw | 4 | 655 | local (hypothesis, binder or field) |
| `hP₀` | `-` | (unresolved: a local, a field or a binder) | - | simp | 15 | 3004 | local (hypothesis, binder or field) |
| `hP₄` | `-` | (unresolved: a local, a field or a binder) | - | rw | 4 | 4883 | local (hypothesis, binder or field) |
| `hP₅` | `-` | (unresolved: a local, a field or a binder) | - | rw | 2 | 4897 | local (hypothesis, binder or field) |
| `hT` | `-` | (unresolved: a local, a field or a binder) | - | rw | 19 | 755 | local (hypothesis, binder or field) |
| `hT'` | `-` | (unresolved: a local, a field or a binder) | - | rw | 8 | 947 | local (hypothesis, binder or field) |
| `hT0` | `-` | (unresolved: a local, a field or a binder) | - | rw,simp | 4 | 2062 | local (hypothesis, binder or field) |
| `hT1` | `-` | (unresolved: a local, a field or a binder) | - | rw,simp | 14 | 2065 | local (hypothesis, binder or field) |
| `hT10` | `-` | (unresolved: a local, a field or a binder) | - | rw | 1 | 4631 | local (hypothesis, binder or field) |
| `hT11` | `-` | (unresolved: a local, a field or a binder) | - | rw,simp | 10 | 3781 | local (hypothesis, binder or field) |
| `hT12` | `-` | (unresolved: a local, a field or a binder) | - | rw,simp | 10 | 3796 | local (hypothesis, binder or field) |
| `hT13` | `-` | (unresolved: a local, a field or a binder) | - | rw,simp | 10 | 3813 | local (hypothesis, binder or field) |
| `hT14` | `-` | (unresolved: a local, a field or a binder) | - | rw,simp | 12 | 3822 | local (hypothesis, binder or field) |
| `hT2` | `-` | (unresolved: a local, a field or a binder) | - | rw,simp | 24 | 3015 | local (hypothesis, binder or field) |
| `hT3` | `-` | (unresolved: a local, a field or a binder) | - | simp | 9 | 3024 | local (hypothesis, binder or field) |
| `hT4` | `-` | (unresolved: a local, a field or a binder) | - | simp | 19 | 3641 | local (hypothesis, binder or field) |
| `hT5` | `-` | (unresolved: a local, a field or a binder) | - | simp | 30 | 3070 | local (hypothesis, binder or field) |
| `hT6` | `-` | (unresolved: a local, a field or a binder) | - | simp | 4 | 3980 | local (hypothesis, binder or field) |
| `hT7` | `-` | (unresolved: a local, a field or a binder) | - | simp | 6 | 3109 | local (hypothesis, binder or field) |
| `hT8` | `-` | (unresolved: a local, a field or a binder) | - | rw,simp | 17 | 3123 | local (hypothesis, binder or field) |
| `hT9` | `-` | (unresolved: a local, a field or a binder) | - | rw,simp | 17 | 3141 | local (hypothesis, binder or field) |
| `hTA` | `-` | (unresolved: a local, a field or a binder) | - | simp | 15 | 3588 | local (hypothesis, binder or field) |
| `hTB` | `-` | (unresolved: a local, a field or a binder) | - | simp | 10 | 3928 | local (hypothesis, binder or field) |
| `hTa` | `-` | (unresolved: a local, a field or a binder) | - | rw | 1 | 1081 | local (hypothesis, binder or field) |
| `hTb` | `-` | (unresolved: a local, a field or a binder) | - | rw | 1 | 1085 | local (hypothesis, binder or field) |
| `hTc` | `-` | (unresolved: a local, a field or a binder) | - | rw | 5 | 1777 | local (hypothesis, binder or field) |
| `hTd` | `-` | (unresolved: a local, a field or a binder) | - | rw | 1 | 1999 | local (hypothesis, binder or field) |
| `hT₀` | `-` | (unresolved: a local, a field or a binder) | - | simp | 16 | 3428 | local (hypothesis, binder or field) |
| `hT₁` | `-` | (unresolved: a local, a field or a binder) | - | rw,simp | 5 | 3441 | local (hypothesis, binder or field) |
| `hT₂` | `-` | (unresolved: a local, a field or a binder) | - | rw,simp | 8 | 4856 | local (hypothesis, binder or field) |
| `hT₃` | `-` | (unresolved: a local, a field or a binder) | - | rw,simp | 6 | 4874 | local (hypothesis, binder or field) |
| `hW` | `-` | (unresolved: a local, a field or a binder) | - | rw | 1 | 4773 | local (hypothesis, binder or field) |
| `hX` | `-` | (unresolved: a local, a field or a binder) | - | rw | 1 | 5187 | local (hypothesis, binder or field) |
| `ha` | `-` | (unresolved: a local, a field or a binder) | - | rw | 4 | 1047 | local (hypothesis, binder or field) |
| `ha.trans_le` | `-` | (unresolved: a local, a field or a binder) | - | rw | 1 | 3229 | local (hypothesis, binder or field) |
| `hab` | `-` | (unresolved: a local, a field or a binder) | - | rw | 1 | 1081 | local (hypothesis, binder or field) |
| `hb` | `-` | (unresolved: a local, a field or a binder) | - | rw | 3 | 1043 | local (hypothesis, binder or field) |
| `hb0` | `-` | (unresolved: a local, a field or a binder) | - | rw | 3 | 2994 | local (hypothesis, binder or field) |
| `hb10` | `-` | (unresolved: a local, a field or a binder) | - | rw | 8 | 4068 | local (hypothesis, binder or field) |
| `hb11` | `-` | (unresolved: a local, a field or a binder) | - | rw | 4 | 4145 | local (hypothesis, binder or field) |
| `hb14` | `-` | (unresolved: a local, a field or a binder) | - | rw | 3 | 4856 | local (hypothesis, binder or field) |
| `hb4` | `-` | (unresolved: a local, a field or a binder) | - | rw | 3 | 4945 | local (hypothesis, binder or field) |
| `hb5` | `-` | (unresolved: a local, a field or a binder) | - | rw | 2 | 3711 | local (hypothesis, binder or field) |
| `hb6` | `-` | (unresolved: a local, a field or a binder) | - | rw | 2 | 3781 | local (hypothesis, binder or field) |
| `hb9` | `-` | (unresolved: a local, a field or a binder) | - | rw | 2 | 3123 | local (hypothesis, binder or field) |
| `hback` | `-` | (unresolved: a local, a field or a binder) | - | rw | 2 | 1165 | local (hypothesis, binder or field) |
| `hbrun` | `-` | (unresolved: a local, a field or a binder) | - | rw | 2 | 1477 | local (hypothesis, binder or field) |
| `hc` | `-` | (unresolved: a local, a field or a binder) | - | rw,simp only | 12 | 879 | local (hypothesis, binder or field) |
| `hc'` | `-` | (unresolved: a local, a field or a binder) | - | rw | 1 | 4447 | local (hypothesis, binder or field) |
| `hcmp` | `-` | (unresolved: a local, a field or a binder) | - | rw | 1 | 3077 | local (hypothesis, binder or field) |
| `hc₀` | `-` | (unresolved: a local, a field or a binder) | - | rw | 1 | 1618 | local (hypothesis, binder or field) |
| `hd` | `-` | (unresolved: a local, a field or a binder) | - | rw | 3 | 1042 | local (hypothesis, binder or field) |
| `hdl` | `-` | (unresolved: a local, a field or a binder) | - | rw,simp only | 3 | 1371 | local (hypothesis, binder or field) |
| `hdst` | `-` | (unresolved: a local, a field or a binder) | - | rw | 3 | 667 | local (hypothesis, binder or field) |
| `he` | `-` | (unresolved: a local, a field or a binder) | - | rw,simp | 5 | 2290 | local (hypothesis, binder or field) |
| `hem` | `-` | (unresolved: a local, a field or a binder) | - | rw | 3 | 1318 | local (hypothesis, binder or field) |
| `hem'` | `-` | (unresolved: a local, a field or a binder) | - | rw | 1 | 1406 | local (hypothesis, binder or field) |
| `hend` | `-` | (unresolved: a local, a field or a binder) | - | rw | 10 | 909 | local (hypothesis, binder or field) |
| `heq` | `-` | (unresolved: a local, a field or a binder) | - | rw | 1 | 1128 | local (hypothesis, binder or field) |
| `hgt` | `-` | (unresolved: a local, a field or a binder) | - | rw,simp | 4 | 1137 | local (hypothesis, binder or field) |
| `hi` | `-` | (unresolved: a local, a field or a binder) | - | rw,simp,simp only | 24 | 2418 | local (hypothesis, binder or field) |
| `hi0` | `-` | (unresolved: a local, a field or a binder) | - | rw | 4 | 959 | local (hypothesis, binder or field) |
| `hid` | `-` | (unresolved: a local, a field or a binder) | - | rw | 1 | 1627 | local (hypothesis, binder or field) |
| `hj` | `-` | (unresolved: a local, a field or a binder) | - | rw | 19 | 668 | local (hypothesis, binder or field) |
| `hjk` | `-` | (unresolved: a local, a field or a binder) | - | rw | 1 | 3248 | local (hypothesis, binder or field) |
| `hk` | `-` | (unresolved: a local, a field or a binder) | - | rw | 3 | 1354 | local (hypothesis, binder or field) |
| `hk1` | `-` | (unresolved: a local, a field or a binder) | - | rw | 4 | 1371 | local (hypothesis, binder or field) |
| `hkb` | `-` | (unresolved: a local, a field or a binder) | - | rw | 2 | 1362 | local (hypothesis, binder or field) |
| `hl12` | `-` | (unresolved: a local, a field or a binder) | - | simp | 1 | 3870 | local (hypothesis, binder or field) |
| `hl16` | `-` | (unresolved: a local, a field or a binder) | - | rw | 1 | 3837 | local (hypothesis, binder or field) |
| `hlast` | `-` | (unresolved: a local, a field or a binder) | - | rw | 1 | 1394 | local (hypothesis, binder or field) |
| `hlt` | `-` | (unresolved: a local, a field or a binder) | - | rw | 6 | 1119 | local (hypothesis, binder or field) |
| `hlt'` | `-` | (unresolved: a local, a field or a binder) | - | rw | 1 | 4098 | local (hypothesis, binder or field) |
| `hlt10` | `-` | (unresolved: a local, a field or a binder) | - | simp | 2 | 3744 | local (hypothesis, binder or field) |
| `hlt7` | `-` | (unresolved: a local, a field or a binder) | - | simp | 2 | 3682 | local (hypothesis, binder or field) |
| `hm` | `-` | (unresolved: a local, a field or a binder) | - | rw,simp | 3 | 3141 | local (hypothesis, binder or field) |
| `hmv` | `-` | (unresolved: a local, a field or a binder) | - | rw | 3 | 1119 | local (hypothesis, binder or field) |
| `hn` | `-` | (unresolved: a local, a field or a binder) | - | rw,simp only | 15 | 1340 | local (hypothesis, binder or field) |
| `hne` | `-` | (unresolved: a local, a field or a binder) | - | rw,simp | 6 | 727 | local (hypothesis, binder or field) |
| `hne0` | `-` | (unresolved: a local, a field or a binder) | - | rw | 1 | 1810 | local (hypothesis, binder or field) |
| `hnx` | `-` | (unresolved: a local, a field or a binder) | - | rw | 1 | 3173 | local (hypothesis, binder or field) |
| `ho2` | `-` | (unresolved: a local, a field or a binder) | - | rw | 1 | 5251 | local (hypothesis, binder or field) |
| `ho3` | `-` | (unresolved: a local, a field or a binder) | - | rw | 2 | 5170 | local (hypothesis, binder or field) |
| `hout` | `-` | (unresolved: a local, a field or a binder) | - | rw | 1 | 1890 | local (hypothesis, binder or field) |
| `hp` | `-` | (unresolved: a local, a field or a binder) | - | rw | 6 | 3250 | local (hypothesis, binder or field) |
| `hpos` | `-` | (unresolved: a local, a field or a binder) | - | rw | 1 | 909 | local (hypothesis, binder or field) |
| `hpre` | `-` | (unresolved: a local, a field or a binder) | - | rw | 2 | 1295 | local (hypothesis, binder or field) |
| `hpre'` | `-` | (unresolved: a local, a field or a binder) | - | rw | 3 | 1477 | local (hypothesis, binder or field) |
| `hq` | `-` | (unresolved: a local, a field or a binder) | - | rw | 21 | 618 | local (hypothesis, binder or field) |
| `hq0` | `-` | (unresolved: a local, a field or a binder) | - | rw | 1 | 5130 | local (hypothesis, binder or field) |
| `hra` | `-` | (unresolved: a local, a field or a binder) | - | rw | 11 | 1102 | local (hypothesis, binder or field) |
| `hrb` | `-` | (unresolved: a local, a field or a binder) | - | rw | 7 | 1102 | local (hypothesis, binder or field) |
| `hrd` | `-` | (unresolved: a local, a field or a binder) | - | rw | 2 | 1416 | local (hypothesis, binder or field) |
| `hrest` | `-` | (unresolved: a local, a field or a binder) | - | rw | 1 | 4016 | local (hypothesis, binder or field) |
| `hrun` | `-` | (unresolved: a local, a field or a binder) | - | rw | 9 | 837 | local (hypothesis, binder or field) |
| `hrunH` | `-` | (unresolved: a local, a field or a binder) | - | rw | 4 | 1637 | local (hypothesis, binder or field) |
| `hs` | `-` | (unresolved: a local, a field or a binder) | - | rw,simp | 46 | 542 | local (hypothesis, binder or field) |
| `hscan` | `-` | (unresolved: a local, a field or a binder) | - | rw | 2 | 1109 | local (hypothesis, binder or field) |
| `hseg` | `-` | (unresolved: a local, a field or a binder) | - | erw,rw | 5 | 4914 | local (hypothesis, binder or field) |
| `hsrc` | `-` | (unresolved: a local, a field or a binder) | - | rw | 4 | 655 | local (hypothesis, binder or field) |
| `hst` | `-` | (unresolved: a local, a field or a binder) | - | rw | 1 | 1885 | local (hypothesis, binder or field) |
| `hstart` | `-` | (unresolved: a local, a field or a binder) | - | rw | 7 | 907 | local (hypothesis, binder or field) |
| `hstep1` | `-` | (unresolved: a local, a field or a binder) | - | rw | 4 | 1371 | local (hypothesis, binder or field) |
| `hstep2` | `-` | (unresolved: a local, a field or a binder) | - | rw | 2 | 1406 | local (hypothesis, binder or field) |
| `hsuf` | `-` | (unresolved: a local, a field or a binder) | - | rw | 2 | 1466 | local (hypothesis, binder or field) |
| `hsuf'` | `-` | (unresolved: a local, a field or a binder) | - | rw | 1 | 1477 | local (hypothesis, binder or field) |
| `hsz` | `-` | (unresolved: a local, a field or a binder) | - | rw | 1 | 435 | local (hypothesis, binder or field) |
| `htr` | `-` | (unresolved: a local, a field or a binder) | - | rw | 1 | 976 | local (hypothesis, binder or field) |
| `hturn` | `-` | (unresolved: a local, a field or a binder) | - | rw | 1 | 1148 | local (hypothesis, binder or field) |
| `hu` | `-` | (unresolved: a local, a field or a binder) | - | rw | 11 | 1102 | local (hypothesis, binder or field) |
| `hu'` | `-` | (unresolved: a local, a field or a binder) | - | rw | 2 | 540 | local (hypothesis, binder or field) |
| `hu0` | `-` | (unresolved: a local, a field or a binder) | - | rw | 3 | 914 | local (hypothesis, binder or field) |
| `hv` | `-` | (unresolved: a local, a field or a binder) | - | rw,simp | 12 | 1102 | local (hypothesis, binder or field) |
| `hv'` | `-` | (unresolved: a local, a field or a binder) | - | simp | 2 | 4096 | local (hypothesis, binder or field) |
| `hw` | `-` | (unresolved: a local, a field or a binder) | - | rw | 2 | 976 | local (hypothesis, binder or field) |
| `hw'` | `-` | (unresolved: a local, a field or a binder) | - | rw,simp | 3 | 1636 | local (hypothesis, binder or field) |
| `hσ` | `-` | (unresolved: a local, a field or a binder) | - | rw | 6 | 1726 | local (hypothesis, binder or field) |
| `hσ0` | `-` | (unresolved: a local, a field or a binder) | - | rw | 8 | 1920 | local (hypothesis, binder or field) |
| `hσ1` | `-` | (unresolved: a local, a field or a binder) | - | rw | 7 | 1918 | local (hypothesis, binder or field) |
| `hσl` | `-` | (unresolved: a local, a field or a binder) | - | rw,show | 7 | 1724 | local (hypothesis, binder or field) |
| `i` | `-` | (unresolved: a local, a field or a binder) | - | rw,show,simp | 40 | 1103 | local (hypothesis, binder or field) |
| `i.castSucc` | `-` | (unresolved: a local, a field or a binder) | - | show | 2 | 1803 | local (hypothesis, binder or field) |
| `i.isLt` | `-` | (unresolved: a local, a field or a binder) | - | rw | 1 | 3292 | local (hypothesis, binder or field) |
| `ih` | `-` | (unresolved: a local, a field or a binder) | - | rw | 10 | 397 | local (hypothesis, binder or field) |
| `ip` | `-` | (unresolved: a local, a field or a binder) | - | rw | 17 | 976 | local (hypothesis, binder or field) |
| `j` | `-` | (unresolved: a local, a field or a binder) | - | rw,show | 59 | 1119 | local (hypothesis, binder or field) |
| `k` | `-` | (unresolved: a local, a field or a binder) | - | rw,show | 25 | 1309 | local (hypothesis, binder or field) |
| `length` | `-` | (unresolved: a local, a field or a binder) | - | rw,show | 3 | 1976 | local (hypothesis, binder or field) |
| `lt` | `-` | (unresolved: a local, a field or a binder) | - | rw | 1 | 1119 | local (hypothesis, binder or field) |
| `m` | `-` | (unresolved: a local, a field or a binder) | - | rw,show | 26 | 1109 | local (hypothesis, binder or field) |
| `n` | `-` | (unresolved: a local, a field or a binder) | - | rw,show | 8 | 1318 | local (hypothesis, binder or field) |
| `neg` | `-` | (unresolved: a local, a field or a binder) | - | rw | 6 | 1112 | local (hypothesis, binder or field) |
| `o` | `-` | (unresolved: a local, a field or a binder) | - | rw,show | 9 | 976 | local (hypothesis, binder or field) |
| `o'` | `-` | (unresolved: a local, a field or a binder) | - | rw | 2 | 1318 | local (hypothesis, binder or field) |
| `omega` | `-` | (unresolved: a local, a field or a binder) | - | rw,unfold | 68 | 618 | local (hypothesis, binder or field) |
| `p` | `-` | (unresolved: a local, a field or a binder) | - | show | 5 | 654 | local (hypothesis, binder or field) |
| `pbc` | `-` | (unresolved: a local, a field or a binder) | - | show | 1 | 2359 | local (hypothesis, binder or field) |
| `pos` | `-` | (unresolved: a local, a field or a binder) | - | rw | 4 | 1103 | local (hypothesis, binder or field) |
| `pre` | `-` | (unresolved: a local, a field or a binder) | - | rw | 2 | 1287 | local (hypothesis, binder or field) |
| `pre.length` | `-` | (unresolved: a local, a field or a binder) | - | rw,show | 14 | 1287 | local (hypothesis, binder or field) |
| `puc` | `-` | (unresolved: a local, a field or a binder) | - | show | 1 | 2327 | local (hypothesis, binder or field) |
| `push_cast` | `-` | (unresolved: a local, a field or a binder) | - | rw | 2 | 620 | local (hypothesis, binder or field) |
| `q` | `-` | (unresolved: a local, a field or a binder) | - | rw,show | 8 | 614 | local (hypothesis, binder or field) |
| `q₀` | `-` | (unresolved: a local, a field or a binder) | - | show | 1 | 5014 | local (hypothesis, binder or field) |
| `r` | `-` | (unresolved: a local, a field or a binder) | - | rw | 2 | 3483 | local (hypothesis, binder or field) |
| `r'` | `-` | (unresolved: a local, a field or a binder) | - | rw | 2 | 3483 | local (hypothesis, binder or field) |
| `rd` | `-` | (unresolved: a local, a field or a binder) | - | rw | 2 | 1295 | local (hypothesis, binder or field) |
| `rest.head?` | `-` | (unresolved: a local, a field or a binder) | - | rw | 2 | 1394 | local (hypothesis, binder or field) |
| `ring` | `-` | (unresolved: a local, a field or a binder) | - | rw | 5 | 614 | local (hypothesis, binder or field) |
| `rintro` | `-` | (unresolved: a local, a field or a binder) | - | rw | 1 | 1394 | local (hypothesis, binder or field) |
| `rr` | `-` | (unresolved: a local, a field or a binder) | - | rw,show | 13 | 1309 | local (hypothesis, binder or field) |
| `runFrom` | `-` | (unresolved: a local, a field or a binder) | - | show | 2 | 5113 | local (hypothesis, binder or field) |
| `rw` | `-` | (unresolved: a local, a field or a binder) | - | rw,show,unfold | 28 | 620 | local (hypothesis, binder or field) |
| `s` | `-` | (unresolved: a local, a field or a binder) | - | rw | 2 | 976 | local (hypothesis, binder or field) |
| `s1` | `-` | (unresolved: a local, a field or a binder) | - | show | 3 | 5014 | local (hypothesis, binder or field) |
| `setup` | `-` | (unresolved: a local, a field or a binder) | - | show | 3 | 5014 | local (hypothesis, binder or field) |
| `simp` | `-` | (unresolved: a local, a field or a binder) | - | rw,unfold | 21 | 1119 | local (hypothesis, binder or field) |
| `src` | `-` | (unresolved: a local, a field or a binder) | - | show | 6 | 654 | local (hypothesis, binder or field) |
| `state` | `-` | (unresolved: a local, a field or a binder) | - | rw | 2 | 976 | local (hypothesis, binder or field) |
| `suf` | `-` | (unresolved: a local, a field or a binder) | - | rw | 4 | 1340 | local (hypothesis, binder or field) |
| `suf.length` | `-` | (unresolved: a local, a field or a binder) | - | rw,show | 11 | 1457 | local (hypothesis, binder or field) |
| `t` | `-` | (unresolved: a local, a field or a binder) | - | rw,show | 5 | 909 | local (hypothesis, binder or field) |
| `tauto` | `-` | (unresolved: a local, a field or a binder) | - | rw | 1 | 1047 | local (hypothesis, binder or field) |
| `tb` | `-` | (unresolved: a local, a field or a binder) | - | rw | 4 | 1477 | local (hypothesis, binder or field) |
| `toList` | `-` | (unresolved: a local, a field or a binder) | - | show | 1 | 2094 | local (hypothesis, binder or field) |
| `u` | `-` | (unresolved: a local, a field or a binder) | - | rw,show | 10 | 620 | local (hypothesis, binder or field) |
| `u.length` | `-` | (unresolved: a local, a field or a binder) | - | rw,show | 4 | 614 | local (hypothesis, binder or field) |
| `v` | `-` | (unresolved: a local, a field or a binder) | - | rw,show | 5 | 1439 | local (hypothesis, binder or field) |
| `w` | `-` | (unresolved: a local, a field or a binder) | - | rw | 1 | 620 | local (hypothesis, binder or field) |
| `w'` | `-` | (unresolved: a local, a field or a binder) | - | rw | 1 | 1798 | local (hypothesis, binder or field) |
| `w.length` | `-` | (unresolved: a local, a field or a binder) | - | rw,show | 3 | 1340 | local (hypothesis, binder or field) |
| `x` | `-` | (unresolved: a local, a field or a binder) | - | rw | 4 | 976 | local (hypothesis, binder or field) |
| `y.length` | `-` | (unresolved: a local, a field or a binder) | - | rw,show | 12 | 2329 | local (hypothesis, binder or field) |
| `κ` | `-` | (unresolved: a local, a field or a binder) | - | show | 6 | 5014 | local (hypothesis, binder or field) |
| `σ` | `-` | (unresolved: a local, a field or a binder) | - | show | 11 | 1799 | local (hypothesis, binder or field) |
| `phaseHostTM` | `Turing.phaseHostTM` | def | TCSlib.Complexity.TuringMachine.Build.Seam | show | 3 | 5014 | other file: definition named in `show` goals that unfold only the file's own `qyM₁` to its `tm`; itself not unfolded (sealed copy elaborates; reviewed) |
| `Cfg.ofWords` | `Turing.Cfg.ofWords` | def | TCSlib.Complexity.TuringMachine.Build.Convention | show | 1 | 5014 | other file: definition named in a `show` goal that unfolds only the file's own `qyM₁` to its `tm`; itself not unfolded (sealed copy elaborates; reviewed) |
| `Cfg` | `Turing.Cfg` | inductive | TCSlib.Complexity.TuringMachine.Configuration | rw | 1 | 976 | other file: inductive (structure field/constructor/type; not unfolded) |
| `Action.apply_inputPos` | `Turing.Action.apply_inputPos` | theorem | TCSlib.Complexity.TuringMachine.Configuration | rw | 1 | 980 | other file: theorem |
| `Action.apply_output` | `Turing.Action.apply_output` | theorem | TCSlib.Complexity.TuringMachine.Configuration | rw | 2 | 989 | other file: theorem |
| `Action.apply_state` | `Turing.Action.apply_state` | theorem | TCSlib.Complexity.TuringMachine.Configuration | rw | 2 | 978 | other file: theorem |
| `Action.apply_workTapePos` | `Turing.Action.apply_workTapePos` | theorem | TCSlib.Complexity.TuringMachine.Configuration | rw | 1 | 987 | other file: theorem |
| `Action.apply_workTapes` | `Turing.Action.apply_workTapes` | theorem | TCSlib.Complexity.TuringMachine.Simulation | rw | 1 | 983 | other file: theorem |
| `Cfg.mapState_inputPos` | `Turing.Cfg.mapState_inputPos` | theorem | TCSlib.Complexity.TuringMachine.StateRenaming | rw | 5 | 504 | other file: theorem |
| `Cfg.mapState_output` | `Turing.Cfg.mapState_output` | theorem | TCSlib.Complexity.TuringMachine.StateRenaming | rw | 8 | 512 | other file: theorem |
| `Cfg.mapState_state` | `Turing.Cfg.mapState_state` | theorem | TCSlib.Complexity.TuringMachine.StateRenaming | rw | 15 | 502 | other file: theorem |
| `Cfg.mapState_workTapePos` | `Turing.Cfg.mapState_workTapePos` | theorem | TCSlib.Complexity.TuringMachine.StateRenaming | rw | 5 | 510 | other file: theorem |
| `Cfg.mapState_workTapes` | `Turing.Cfg.mapState_workTapes` | theorem | TCSlib.Complexity.TuringMachine.StateRenaming | rw | 5 | 507 | other file: theorem |
| `Cfg.ofWords_inputPos` | `Turing.Cfg.ofWords_inputPos` | theorem | TCSlib.Complexity.TuringMachine.Build.Convention | rw | 5 | 881 | other file: theorem |
| `Cfg.ofWords_output` | `Turing.Cfg.ofWords_output` | theorem | TCSlib.Complexity.TuringMachine.Build.Convention | rw | 7 | 889 | other file: theorem |
| `Cfg.ofWords_state` | `Turing.Cfg.ofWords_state` | theorem | TCSlib.Complexity.TuringMachine.Build.Convention | rw | 7 | 895 | other file: theorem |
| `Cfg.ofWords_workTapePos` | `Turing.Cfg.ofWords_workTapePos` | theorem | TCSlib.Complexity.TuringMachine.Build.Convention | rw | 5 | 887 | other file: theorem |
| `Cfg.ofWords_workTapes` | `Turing.Cfg.ofWords_workTapes` | theorem | TCSlib.Complexity.TuringMachine.Build.Convention | rw | 5 | 884 | other file: theorem |
| `Cfg.stopped_iff` | `Turing.Cfg.stopped_iff` | theorem | TCSlib.Complexity.TuringMachine.Build.StepClock | rw | 2 | 1530 | other file: theorem |
| `Cfg.workTapeSymbols_eq` | `Turing.Cfg.workTapeSymbols_eq` | theorem | TCSlib.Complexity.TuringMachine.Configuration | rw | 2 | 974 | other file: theorem |
| `FinTM.bufferTape_eq` | `Turing.FinTM.bufferTape_eq` | theorem | TCSlib.Complexity.TuringMachine.Simulation | rw | 5 | 618 | other file: theorem |
| `FinTM.bufferTape_eq_none_of_not_mem` | `Turing.FinTM.bufferTape_eq_none_of_not_mem` | theorem | TCSlib.Complexity.TuringMachine.BufferWords | rw | 8 | 620 | other file: theorem |
| `FinTM.bufferTape_left` | `Turing.FinTM.bufferTape_left` | theorem | TCSlib.Complexity.TuringMachine.Simulation | rw | 1 | 1168 | other file: theorem |
| `FinTM.bufferTape_nat` | `Turing.FinTM.bufferTape_nat` | theorem | TCSlib.Complexity.TuringMachine.Simulation | rw | 13 | 1096 | other file: theorem |
| `FinTM.bufferTape_nil` | `Turing.FinTM.bufferTape_nil` | theorem | TCSlib.Complexity.TuringMachine.Simulation | rw | 3 | 736 | other file: theorem |
| `MultiTapeTM.runFrom_add` | `Turing.MultiTapeTM.runFrom_add` | theorem | TCSlib.Complexity.TuringMachine.Deterministic | rw | 17 | 1406 | other file: theorem |
| `MultiTapeTM.runFrom_succ_eq_step'` | `Turing.MultiTapeTM.runFrom_succ_eq_step'` | theorem | TCSlib.Complexity.TuringMachine.Deterministic | rw | 12 | 1094 | other file: theorem |
| `MultiTapeTM.runFrom_zero` | `Turing.MultiTapeTM.runFrom_zero` | theorem | TCSlib.Complexity.TuringMachine.Deterministic | rw | 12 | 911 | other file: theorem |
| `MultiTapeTM.step_of_some` | `Turing.MultiTapeTM.step_of_some` | theorem | TCSlib.Complexity.TuringMachine.Deterministic | rw | 2 | 976 | other file: theorem |
| `clockCfg_inputPos` | `Turing.clockCfg_inputPos` | theorem | TCSlib.Complexity.TuringMachine.Build.StepClock | rw | 2 | 1719 | other file: theorem |
| `clockCfg_output` | `Turing.clockCfg_output` | theorem | TCSlib.Complexity.TuringMachine.Build.StepClock | rw | 3 | 1646 | other file: theorem |
| `clockCfg_state` | `Turing.clockCfg_state` | theorem | TCSlib.Complexity.TuringMachine.Build.StepClock | rw | 3 | 1645 | other file: theorem |
| `clockCfg_workTapePos` | `Turing.clockCfg_workTapePos` | theorem | TCSlib.Complexity.TuringMachine.Build.StepClock | rw | 2 | 1729 | other file: theorem |
| `clockCfg_workTapes` | `Turing.clockCfg_workTapes` | theorem | TCSlib.Complexity.TuringMachine.Build.StepClock | rw | 2 | 1722 | other file: theorem |
| `counterValue_bits` | `Turing.counterValue_bits` | theorem | TCSlib.Complexity.TuringMachine.Build.CounterLoop | rw | 1 | 2934 | other file: theorem |
| `counterValue_eq` | `Turing.counterValue_eq` | theorem | TCSlib.Complexity.TuringMachine.Build.CounterLoop | rw | 1 | 2934 | other file: theorem |
| `counter_cfg_eq` | `Turing.counter_cfg_eq` | theorem | TCSlib.Complexity.TuringMachine.Build.CounterLoop | rw | 2 | 1911 | other file: theorem |
| `embedEmitCfg_output` | `Turing.embedEmitCfg_output` | theorem | TCSlib.Complexity.TuringMachine.Build.Embed | rw | 1 | 1890 | other file: theorem |
| `embedEmitCfg_state` | `Turing.embedEmitCfg_state` | theorem | TCSlib.Complexity.TuringMachine.Build.Embed | rw | 2 | 848 | other file: theorem |
| `embedEmitTM_runFrom` | `Turing.embedEmitTM_runFrom` | theorem | TCSlib.Complexity.TuringMachine.Build.Embed | rw | 1 | 822 | other file: theorem |
| `initCfg_ofWords` | `Turing.initCfg_ofWords` | theorem | TCSlib.Complexity.TuringMachine.Build.Convention | rw | 1 | 5013 | other file: theorem |
| `moveInputPos_zero` | `Turing.moveInputPos_zero` | theorem | TCSlib.Complexity.TuringMachine.Configuration | rw | 1 | 980 | other file: theorem |
| `pairEncode_eq` | `Turing.pairEncode_eq` | theorem | TCSlib.Complexity.TuringMachine.Encoding | rw | 2 | 4773 | other file: theorem |
| `phaseHostTM_q₀` | `Turing.phaseHostTM_q₀` | theorem | TCSlib.Complexity.TuringMachine.Build.Seam | rw | 1 | 5016 | other file: theorem |
| `seamReleaseTM_runFrom_pos` | `Turing.seamReleaseTM_runFrom_pos` | theorem | TCSlib.Complexity.TuringMachine.Build.Seam | rw | 5 | 909 | other file: theorem |
| `stateWord_eq` | `Turing.stateWord_eq` | theorem | TCSlib.Complexity.TuringMachine.Build.Loop | rw | 9 | 955 | other file: theorem |
| `wordPatch_of_mem` | `Turing.wordPatch_of_mem` | theorem | TCSlib.Complexity.TuringMachine.Build.StepClock | rw | 1 | 1659 | other file: theorem |
| `wordPatch_of_not_mem` | `Turing.wordPatch_of_not_mem` | theorem | TCSlib.Complexity.TuringMachine.Build.StepClock | rw | 1 | 1660 | other file: theorem |
| `QyCmp.back` | `_private.evidence.seal.QyInspect.0.Turing.NTimeDiag.QyCmp.back` | ctor | (this file) | rw | 3 | 1119 | own file |
| `QyCmp.scan` | `_private.evidence.seal.QyInspect.0.Turing.NTimeDiag.QyCmp.scan` | ctor | (this file) | rw | 3 | 1119 | own file |
| `QyEm` | `_private.evidence.seal.QyInspect.0.Turing.NTimeDiag.QyEm` | inductive | (this file) | rw | 1 | 2088 | own file |
| `QyEm.done` | `_private.evidence.seal.QyInspect.0.Turing.NTimeDiag.QyEm.done` | ctor | (this file) | rw | 1 | 2088 | own file |
| `QyKit.K` | `_private.evidence.seal.QyInspect.0.Turing.NTimeDiag.QyKit.K` | def | (this file) | unfold | 11 | 2395 | own file |
| `QyKit.bAb0_ne` | `_private.evidence.seal.QyInspect.0.Turing.NTimeDiag.QyKit.bAb0_ne` | theorem | (this file) | simp | 1 | 3783 | own file |
| `QyKit.bAbJ_ne` | `_private.evidence.seal.QyInspect.0.Turing.NTimeDiag.QyKit.bAbJ_ne` | theorem | (this file) | simp | 1 | 4069 | own file |
| `QyKit.bAbK_ne` | `_private.evidence.seal.QyInspect.0.Turing.NTimeDiag.QyKit.bAbK_ne` | theorem | (this file) | simp | 2 | 4146 | own file |
| `QyKit.bCf` | `_private.evidence.seal.QyInspect.0.Turing.NTimeDiag.QyKit.bCf` | def | (this file) | unfold | 6 | 2509 | own file |
| `QyKit.bCf_ne` | `_private.evidence.seal.QyInspect.0.Turing.NTimeDiag.QyKit.bCf_ne` | theorem | (this file) | simp | 1 | 3442 | own file |
| `QyKit.bCg_ne` | `_private.evidence.seal.QyInspect.0.Turing.NTimeDiag.QyKit.bCg_ne` | theorem | (this file) | rw | 1 | 4858 | own file |
| `QyKit.bCl_ne` | `_private.evidence.seal.QyInspect.0.Turing.NTimeDiag.QyKit.bCl_ne` | theorem | (this file) | rw | 1 | 4658 | own file |
| `QyKit.bClk` | `_private.evidence.seal.QyInspect.0.Turing.NTimeDiag.QyKit.bClk` | def | (this file) | unfold | 4 | 3291 | own file |
| `QyKit.bClk_castSucc` | `_private.evidence.seal.QyInspect.0.Turing.NTimeDiag.QyKit.bClk_castSucc` | theorem | (this file) | rw | 1 | 3363 | own file |
| `QyKit.bPb_ne` | `_private.evidence.seal.QyInspect.0.Turing.NTimeDiag.QyKit.bPb_ne` | theorem | (this file) | rw | 1 | 4947 | own file |
| `QyKit.bPr_ne` | `_private.evidence.seal.QyInspect.0.Turing.NTimeDiag.QyKit.bPr_ne` | theorem | (this file) | simp | 1 | 3124 | own file |
| `QyKit.bPu_ne` | `_private.evidence.seal.QyInspect.0.Turing.NTimeDiag.QyKit.bPu_ne` | theorem | (this file) | simp | 1 | 3713 | own file |
| `QyKit.cbA` | `_private.evidence.seal.QyInspect.0.Turing.NTimeDiag.QyKit.cbA` | def (projection) | (this file) | show | 1 | 3046 | own file |
| `QyKit.hft` | `_private.evidence.seal.QyInspect.0.Turing.NTimeDiag.QyKit.hft` | theorem (projection) | (this file) | rw | 1 | 3483 | own file |
| `QyKit.m` | `_private.evidence.seal.QyInspect.0.Turing.NTimeDiag.QyKit.m` | def | (this file) | unfold | 4 | 3172 | own file |
| `QyKit.tp_inj` | `_private.evidence.seal.QyInspect.0.Turing.NTimeDiag.QyKit.tp_inj` | theorem | (this file) | simp | 51 | 3157 | own file |
| `QyKit.tp_ne` | `_private.evidence.seal.QyInspect.0.Turing.NTimeDiag.QyKit.tp_ne` | theorem | (this file) | rw,simp | 21 | 3004 | own file |
| `QyKit.tp_val` | `_private.evidence.seal.QyInspect.0.Turing.NTimeDiag.QyKit.tp_val` | theorem | (this file) | rw,unfold | 22 | 2458 | own file |
| `QyLK.isEsc` | `_private.evidence.seal.QyInspect.0.Turing.NTimeDiag.QyLK.isEsc` | def | (this file) | simp_all | 1 | 5052 | own file |
| `QyLPh` | `_private.evidence.seal.QyInspect.0.Turing.NTimeDiag.QyLPh` | def | (this file) | dsimp only | 2 | 2563 | own file |
| `QyMPh` | `_private.evidence.seal.QyInspect.0.Turing.NTimeDiag.QyMPh` | def | (this file) | dsimp only | 2 | 2800 | own file |
| `QyMainPh` | `_private.evidence.seal.QyInspect.0.Turing.NTimeDiag.QyMainPh` | def | (this file) | dsimp only | 2 | 2848 | own file |
| `QySPh` | `_private.evidence.seal.QyInspect.0.Turing.NTimeDiag.QySPh` | def | (this file) | dsimp only | 2 | 2695 | own file |
| `QyTPh` | `_private.evidence.seal.QyInspect.0.Turing.NTimeDiag.QyTPh` | def | (this file) | dsimp only | 2 | 2751 | own file |
| `budget_eq` | `Turing.NTimeDiag.budget_eq` | theorem | (this file) | rw | 2 | 379 | own file |
| `ladder_succ` | `Turing.NTimeDiag.ladder_succ` | theorem | (this file) | rw | 1 | 379 | own file |
| `ladder_zero` | `Turing.NTimeDiag.ladder_zero` | theorem | (this file) | rw | 2 | 465 | own file |
| `query_eq` | `Turing.NTimeDiag.query_eq` | theorem | (this file) | rw | 2 | 5170 | own file |
| `query_of_not_guard` | `Turing.NTimeDiag.query_of_not_guard` | theorem | (this file) | rw | 1 | 5251 | own file |
| `qyAnc` | `_private.evidence.seal.QyInspect.0.Turing.NTimeDiag.qyAnc` | def | (this file) | unfold | 3 | 4039 | own file |
| `qyAt` | `_private.evidence.seal.QyInspect.0.Turing.NTimeDiag.qyAt` | def | (this file) | unfold | 1 | 5127 | own file |
| `qyAt2` | `_private.evidence.seal.QyInspect.0.Turing.NTimeDiag.qyAt2` | def | (this file) | rw,unfold | 7 | 1119 | own file |
| `qyAt2_move` | `_private.evidence.seal.QyInspect.0.Turing.NTimeDiag.qyAt2_move` | theorem | (this file) | rw | 4 | 1103 | own file |
| `qyBank` | `_private.evidence.seal.QyInspect.0.Turing.NTimeDiag.qyBank` | def | (this file) | simp only | 1 | 2438 | own file |
| `qyBank_val` | `_private.evidence.seal.QyInspect.0.Turing.NTimeDiag.qyBank_val` | theorem | (this file) | rw | 5 | 2514 | own file |
| `qyBank_zero` | `_private.evidence.seal.QyInspect.0.Turing.NTimeDiag.qyBank_zero` | theorem | (this file) | rw | 3 | 2510 | own file |
| `qyBody` | `_private.evidence.seal.QyInspect.0.Turing.NTimeDiag.qyBody` | def | (this file) | simp,unfold | 2 | 5252 | own file |
| `qyC` | `_private.evidence.seal.QyInspect.0.Turing.NTimeDiag.qyC` | def | (this file) | dsimp only,rw | 12 | 657 | own file |
| `qyC_mapState` | `_private.evidence.seal.QyInspect.0.Turing.NTimeDiag.qyC_mapState` | theorem | (this file) | rw | 6 | 534 | own file |
| `qyCk` | `_private.evidence.seal.QyInspect.0.Turing.NTimeDiag.qyCk` | def | (this file) | unfold | 2 | 4331 | own file |
| `qyCmpTM` | `_private.evidence.seal.QyInspect.0.Turing.NTimeDiag.qyCmpTM` | def | (this file) | rw,simp only | 16 | 1101 | own file |
| `qyDk` | `_private.evidence.seal.QyInspect.0.Turing.NTimeDiag.qyDk` | def | (this file) | unfold | 1 | 4360 | own file |
| `qyEmitTM` | `_private.evidence.seal.QyInspect.0.Turing.NTimeDiag.qyEmitTM` | def | (this file) | rw,simp only | 20 | 1287 | own file |
| `qyLay` | `_private.evidence.seal.QyInspect.0.Turing.NTimeDiag.qyLay` | def | (this file) | simp | 37 | 3157 | own file |
| `qyLayT` | `_private.evidence.seal.QyInspect.0.Turing.NTimeDiag.qyLayT` | def | (this file) | simp,unfold | 29 | 3428 | own file |
| `qyLoc` | `_private.evidence.seal.QyInspect.0.Turing.NTimeDiag.qyLoc` | def | (this file) | unfold | 5 | 3425 | own file |
| `qyLocRed` | `_private.evidence.seal.QyInspect.0.Turing.NTimeDiag.qyLocRed` | def | (this file) | simp,simp only | 70 | 3433 | own file |
| `qyLoopA` | `_private.evidence.seal.QyInspect.0.Turing.NTimeDiag.qyLoopA` | def | (this file) | unfold | 1 | 4493 | own file |
| `qyMainA` | `_private.evidence.seal.QyInspect.0.Turing.NTimeDiag.qyMainA` | def | (this file) | unfold | 2 | 5145 | own file |
| `qyMainM` | `_private.evidence.seal.QyInspect.0.Turing.NTimeDiag.qyMainM` | def | (this file) | show | 3 | 5014 | own file |
| `qyMainRed` | `_private.evidence.seal.QyInspect.0.Turing.NTimeDiag.qyMainRed` | def | (this file) | show,simp,simp_all | 14 | 5038 | own file |
| `qyMid` | `_private.evidence.seal.QyInspect.0.Turing.NTimeDiag.qyMid` | def | (this file) | unfold | 2 | 4705 | own file |
| `qyMidB` | `_private.evidence.seal.QyInspect.0.Turing.NTimeDiag.qyMidB` | def | (this file) | unfold | 2 | 4907 | own file |
| `qyMidRed` | `_private.evidence.seal.QyInspect.0.Turing.NTimeDiag.qyMidRed` | def | (this file) | simp | 13 | 4708 | own file |
| `qyRndP` | `_private.evidence.seal.QyInspect.0.Turing.NTimeDiag.qyRndP` | def | (this file) | unfold | 2 | 4282 | own file |
| `qyRndS` | `_private.evidence.seal.QyInspect.0.Turing.NTimeDiag.qyRndS` | def | (this file) | unfold | 4 | 4259 | own file |
| `qySetB` | `_private.evidence.seal.QyInspect.0.Turing.NTimeDiag.qySetB` | def | (this file) | unfold | 4 | 3172 | own file |
| `qySetF` | `_private.evidence.seal.QyInspect.0.Turing.NTimeDiag.qySetF` | def | (this file) | simp,simp only | 15 | 3000 | own file |
| `qySetRed` | `_private.evidence.seal.QyInspect.0.Turing.NTimeDiag.qySetRed` | def | (this file) | simp | 20 | 2998 | own file |
| `qySetT5` | `_private.evidence.seal.QyInspect.0.Turing.NTimeDiag.qySetT5` | def | (this file) | simp | 12 | 3070 | own file |
| `qyTA` | `_private.evidence.seal.QyInspect.0.Turing.NTimeDiag.qyTA` | def | (this file) | simp | 20 | 3588 | own file |
| `qyTB` | `_private.evidence.seal.QyInspect.0.Turing.NTimeDiag.qyTB` | def | (this file) | simp | 16 | 3867 | own file |
| `qyTestP` | `_private.evidence.seal.QyInspect.0.Turing.NTimeDiag.qyTestP` | def | (this file) | simp only,unfold | 2 | 3569 | own file |
| `qyTestS` | `_private.evidence.seal.QyInspect.0.Turing.NTimeDiag.qyTestS` | def | (this file) | simp only,unfold | 3 | 3569 | own file |
| `qyTop` | `_private.evidence.seal.QyInspect.0.Turing.NTimeDiag.qyTop` | def | (this file) | unfold | 2 | 4733 | own file |
| `qyTopB` | `_private.evidence.seal.QyInspect.0.Turing.NTimeDiag.qyTopB` | def | (this file) | unfold | 2 | 4996 | own file |
| `qyTopRed` | `_private.evidence.seal.QyInspect.0.Turing.NTimeDiag.qyTopRed` | def | (this file) | simp | 11 | 4736 | own file |
| `qyWk` | `_private.evidence.seal.QyInspect.0.Turing.NTimeDiag.qyWk` | def | (this file) | unfold | 2 | 5065 | own file |
| `qy_bits_val` | `_private.evidence.seal.QyInspect.0.Turing.NTimeDiag.qy_bits_val` | theorem | (this file) | rw | 2 | 3043 | own file |
| `qy_bufferTape_map` | `_private.evidence.seal.QyInspect.0.Turing.NTimeDiag.qy_bufferTape_map` | theorem | (this file) | rw | 3 | 666 | own file |
| `qy_embed_gen` | `_private.evidence.seal.QyInspect.0.Turing.NTimeDiag.qy_embed_gen` | theorem | (this file) | rw | 3 | 837 | own file |
| `qy_embed_state` | `_private.evidence.seal.QyInspect.0.Turing.NTimeDiag.qy_embed_state` | theorem | (this file) | rw | 5 | 960 | own file |
| `qy_flatMap_dbl_dbl` | `_private.evidence.seal.QyInspect.0.Turing.NTimeDiag.qy_flatMap_dbl_dbl` | theorem | (this file) | rw | 1 | 4773 | own file |
| `qy_initCfg` | `_private.evidence.seal.QyInspect.0.Turing.NTimeDiag.qy_initCfg` | theorem | (this file) | rw | 2 | 5112 | own file |
| `qy_ladder_succ_eq` | `_private.evidence.seal.QyInspect.0.Turing.NTimeDiag.qy_ladder_succ_eq` | theorem | (this file) | rw | 2 | 4444 | own file |
| `qy_log_bits` | `_private.evidence.seal.QyInspect.0.Turing.NTimeDiag.qy_log_bits` | theorem | (this file) | rw | 3 | 3229 | own file |
| `qy_moveOne` | `_private.evidence.seal.QyInspect.0.Turing.NTimeDiag.qy_moveOne` | theorem | (this file) | rw | 1 | 1362 | own file |
| `qy_noMove` | `_private.evidence.seal.QyInspect.0.Turing.NTimeDiag.qy_noMove` | theorem | (this file) | rw | 9 | 1287 | own file |
| `qy_ones_val` | `_private.evidence.seal.QyInspect.0.Turing.NTimeDiag.qy_ones_val` | theorem | (this file) | rw | 1 | 1631 | own file |
| `qy_run_one` | `_private.evidence.seal.QyInspect.0.Turing.NTimeDiag.qy_run_one` | theorem | (this file) | rw | 3 | 1340 | own file |
| `qy_run_two` | `_private.evidence.seal.QyInspect.0.Turing.NTimeDiag.qy_run_two` | theorem | (this file) | rw | 2 | 1371 | own file |
| `qy_rung_val` | `_private.evidence.seal.QyInspect.0.Turing.NTimeDiag.qy_rung_val` | theorem | (this file) | rwa | 1 | 3810 | own file |
| `qy_step` | `_private.evidence.seal.QyInspect.0.Turing.NTimeDiag.qy_step` | theorem | (this file) | rw | 15 | 1119 | own file |
| `qy_unpair_succ_diag` | `_private.evidence.seal.QyInspect.0.Turing.NTimeDiag.qy_unpair_succ_diag` | theorem | (this file) | rw | 1 | 4152 | own file |
| `qy_unpair_succ_gt` | `_private.evidence.seal.QyInspect.0.Turing.NTimeDiag.qy_unpair_succ_gt` | theorem | (this file) | rw | 1 | 4181 | own file |
| `qy_unpair_succ_last` | `_private.evidence.seal.QyInspect.0.Turing.NTimeDiag.qy_unpair_succ_last` | theorem | (this file) | rw | 1 | 4116 | own file |
| `qy_unpair_succ_lt` | `_private.evidence.seal.QyInspect.0.Turing.NTimeDiag.qy_unpair_succ_lt` | theorem | (this file) | rw | 1 | 4098 | own file |
| `qy_wordPatch_ones` | `_private.evidence.seal.QyInspect.0.Turing.NTimeDiag.qy_wordPatch_ones` | theorem | (this file) | rw | 1 | 1798 | own file |
| `qy_writer_word` | `_private.evidence.seal.QyInspect.0.Turing.NTimeDiag.qy_writer_word` | theorem | (this file) | rw | 2 | 4916 | own file |
| `stageCode_eq` | `Turing.NTimeDiag.stageCode_eq` | theorem | (this file) | rw | 2 | 5170 | own file |
