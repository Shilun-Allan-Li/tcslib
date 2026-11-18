# Straightforward existing Correctness stubs

Eight unelaborated replacement bodies are staged, with no source edits or Lean run.
The two selection snippets reuse public List APIs; see selection-notes.md. The five
packing snippets rewrite only the published Samplers packSeed_fst/packSeed_snd reader
and Mathlib Equiv.symm_apply_apply (`Logic/Equiv/Defs.lean:251`), then constructor
reduction closes the concrete coordinate. They do not inspect Params' explicit
equivalence implementation or unfold a foreign packing definition.

`08-oneFlag_bounds` reads oneFlag_eq, applies core `of_decide_eq_true`
(`Init/Prelude.lean:987`), rewrites the published cap_eq and public pow_two theorem,
and converts the capacity event through Buckets.overfull_iff. It does not unfold
Bool decide, buckets, capacities, or the error predicate.

All eight bodies depend only on already-proved owner readers and public Core/Mathlib
lemmas, not on current sorried correctness results. They are suitable early checks
once the M0 checkpoint has been pushed. Each snippet was written separately with
exactly one outer tactic block and no nested by. Implicit parameter/Boolean coercion
elaboration remains the lead's check, not a result asserted by these notes.
No generic List theorem, coordinate enumeration, primitive efficiency proof, or new
helper statement is added.
