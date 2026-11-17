# bp progress (U4 BarringtonConverse)

## Plan
- Helpers (private, in namespace BranchingProgram): `maxDepth_le_of_forall`, `maxFaninL_le_of_forall` (Addendum A family);
  eval of empty gates (inline via `eval_node_true_iff`/`eval_node_false_iff`); `maxFanin_wireComp_le` (wireComp fan-in <= 2);
  list-level `compTree` eval/depth/fan-in by well-founded recursion on the list length mirroring `compTree`.
- C17 by `Instr.wire_eq`, `Instr.eval_eq`, split_ifs, `eval_lit`, `Lit.eval_eq`, `depth_lit`, `maxFanin_lit`, `depth_node`, `maxFanin_node`.
- C18 by `wireComp_eq`, `balanced_eval`, `eval_node_false_iff`, `eval_node_true_iff`, `depth_balanced_le`.
- C19 by list helpers; `yield_nil`, `yield_append` (frozen U1), `yield_eq` + List.foldl equations for singleton, `append_instrs` + structure eta.
- C20/C21 by `toFormula_eq`, balanced lemmas, `Finset.length_toList`, `Finset.card_le_univ`, `Fintype.card_fun`, `Nat.clog_le_iff_le_pow`, `Nat.le_pow_clog`, `Nat.pow_le_pow_left`.
2026-11-17T11:21:39Z plan written; waiting for seed; 0/11 proved
2026-11-17T11:23:03Z NOTE for lead: duplication rule -> I will cite U8's frozen F3 lemmas TreeCircuit.const_eq/const_eval/depth_const/maxFanin_const and and2_eq/and2_eval/depth_and2_le/maxFanin_and2_le (Combinators, sorry at base) instead of re-deriving empty-gate/binary-gate facts; the U4 sorryAx trace will then name F3 as well as C1.
2026-11-17T11:26:30Z IMPORT REQUEST (lead please answer): add 'import Mathlib.Data.Fintype.BigOperators' to BarringtonConverse.lean for Fintype.card_fun/Finset.card_le_univ (C21 depth). See scope-request/IMPORT-REQUEST-bp-1.md. Conv-001: 10/11 targets compile; only depth_toFormula_le fails (no Fintype (Fin w → Fin w) in closure).
2026-11-17T11:28:44Z ALL 11 targets proved (Conv-002.log rc 0, 0 errors, 0 sorry); import added per approval; axiom trace: only C1 yield_nil/yield_append and F3 const_*/and2_* (ConvTrace-001.log); local-irreducible seal probe ConvSeal-003 rc 0. Snapshot snapshots/BarringtonConverse-all11.lean.
