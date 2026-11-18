# BilinearGen.dlinMatrixAdv_le candidate

Status: scratch proof assembly, inspection only; native verification pending. No Lean/lake/
build/Git/live edit/extra agent was run. Frozen main header/prose exact; one tactic block,
no holes/sorry/new helper/import or algorithm changes; ≤100 columns. This invocation stops
after this one proof block.

Read dlinMatrixAdv_eq/dlinAdv_eq and the shared advantage_eq twice. Substitute the existing
real acceptance equality. abs_sub_le inserts the canonical FALSE acceptance between the
matrix FALSE and common TRUE acceptances. The random-gap theorem bounds the first absolute
gap by dlinMatrixSlack. add_le_add_right preserves the second (canonical advantage) term;
add_comm puts the final sum in the frozen order. The slack occurs exactly once.

No generic triangle inequality or advantage fact is re-proved. No assumption/efficiency
premise, public algorithm, group representation, sampler or direct MDDH reduction is changed.
Only published readers and ordinary ordered-additive-group lemmas appear in rw/calc.

## Actual searches / source references

Read current Pairing/Linear.lean around :232-241, :294-306 and :320-357 for exact advantage
readers, real acceptance/random gap premises and frozen dlinMatrixAdv_le header (345).
Read Games/Advantage.lean:70-80 for advantage_eq (76). Searched abs_sub_le/accept and the
advantage_triangle family in Pairing/Games; Games/Advantage.lean:103-105 already uses the
same Mathlib abs_sub_le _ _ _ at exactly this three-acceptance shape. A narrow declaration
search in Mathlib Group/{Abs,Basic}.lean did not locate its source declaration, so no source
line claim is made for that Mathlib lemma; its exact usable shape is verified by the existing
published advantage_triangle proof.

Dependencies: existing equation readers, pending dlinMatrixGame_real_accept, pending
dlinMatrixGame_random_gap_le, and standard abs_sub_le/add_le_add_right/add_comm. The generic
dlinDiagonal_random_gap_le prerequisite is now parent-reported native PASS/zero admissions,
but both concrete game identities remain native-pending consumer drafts in the observed
source. No standard-only completed DLIN-comparison chain is claimed until root integrates
and checks those dependencies and this block.
