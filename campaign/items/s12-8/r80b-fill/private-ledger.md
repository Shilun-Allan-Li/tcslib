# Private ledger

**24 → 23:** two additions, three removals. Every change is listed below; all other privates are unchanged.

| Private | Disposition and role |
|---|---|
| `counter_layout` | Added: the existing layout proof moved to its generic form; `counter_cfg_eq` instantiates it. |
| `counter_refl_agree` | Added: table agreement of the prescribed hosts at the identity embedding. |
| `counter_last_unselected` | Removed: its one-use proof is inlined into `counter_layout`. |
| `counter_patch_initial` | Removed: its one-use proof is inlined into the round-zero case. |
| `counter_orbit_succ` | Removed: its one-use invocation is replaced by `Function.iterate_succ_apply'`. |
| `counter_buffer_complement` | Rewritten: direct public buffer-map instance, disposition (i). |
| `counterSpan` | Rewritten: alphabet-generic trajectory predicate; body unchanged. |
| `counter_span_append` | Rewritten: alphabet-generic segment composition; proof unchanged. |
| `counterPatch` | Rewritten: alphabet-generic counter interval overwrite. |
| `counter_patch_twice` | Rewritten: alphabet-generic equal-width overwrite identity. |
| `counter_patch_frame` | Rewritten: alphabet-generic delimiter preservation. |
| `counter_debit` | Rewritten: one-tape decrement through overlay, R1 and guarded state transport. |
| `counter_body` | Rewritten: generic types/host/layout substitutions; same guarded R1 route. |
| `counter_rounds` | Rewritten: the existing single induction, with embedded counter words. |


Final source: 1,697 lines; 87,771 bytes.
