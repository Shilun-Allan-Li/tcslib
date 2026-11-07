# Internal review: the linear-space/NP consumer

**PASS for the reviewed source and checks: 0 blockers, 0 majors, 0 minors, 4 notes.** This is
internal maintainer support, not gate 116's external audit or permission to merge. The parent
maintainer handles the current-campaign replay, serialized screen, PR and external dispatch.

Reviewed base: `96daf38bc82ea21dab18da257fc517ca0bd59ff6`. Reviewed full Hierarchy source SHA-256:
`1d7e0c7d706521991a623dfe6963650f867edfebe34c2dae8316e2078dc8069f`. The source is pinned by content because the proof was an uncommitted
worktree change when this review started; the parent will pin the published PR commit.

## Findings/dispositions

| # | Severity | Observation | Disposition |
|---|---|---|---|
| 1 | note | The source surface stays 4 public / 43 private declarations. Compilation adds one non-private internal proof auxiliary, `Complexity.SPACE_linear_ne_NP._proof_1_1`. Non-private constants are 4 → 5; the full module is 137 → 138 constants, including 133 private constants on each side. | Disclose the compiler/source distinction in the pack. No new source API, definition, host or statement is introduced. |
| 2 | note | Policy lint has the same two inherited findings (the module lacks a Main definitions heading and exceeds the size threshold); campaign lint stays 0 FAIL / 1 inherited size WARN. | No new policy finding. The standing size ruling applies. No cosmetic source repair was made by this reviewer. |
| 3 | note | The strong seal covers the newly changed target section against its four direct foreign definitions, with no exclusions. It is not a seal of the unchanged legacy Hierarchy proofs. The unchanged private padding helper remains same-home. | Keep this scope explicit. The primary `Inventory.lean.txt` documents target-plus-auxiliary scope accurately; the parent's earlier inherited-comment probe is preliminary evidence only. |
| 4 | note | This reviewer did not run a copy-text screen, merged-tree replay, or new independent textbook-source audit. No blueprint file changes and no public name changes occur. | The parent supplies replay/screen; the external auditor supplies the requested fidelity analysis. Blueprint editing/strict regeneration is not triggered by this proof-body-only change. |

## Source and reuse checks

`source.diff` has exactly the approved Padding import and the target proof replacing its `sorry`.
All 47 surviving declaration texts are identical except that proof body; complete top-level
headers, visibility and relative order are unchanged. `headers-base.json`/`headers-head.json`
compare complete headers, and `header-parser-control.json` verifies a nested `input := x` is
retained rather than mistaken for a proof delimiter. Source lines are 2505 → 2518. Existing
source admissions are 2 → 1, leaving only `Complexity.space_universal`.

The proof consumes the already-proved `space_hierarchy`, the unchanged same-home helper
`sph_linear_ne_NP_of_padding`, and `mem_SPACE_padLang` at C = 1, d = 2, T m = m + 1. The only
language conversion is `Set.ext` with the published `mem_padLang_iff`. The elementary inequality
uses Mathlib's `Nat.pow_le_pow_left`. No machine, host, private library API, configuration
extensionality, buffer indexing or copied semantic argument is introduced. The existing proof
sketch describes the route accurately. `argument-inspection.md` lists every new rewrite/reduction
argument; the only explicit rewrite target is a locally proved equality.

Boundary review: at input length 0 the pad has length 1 and the paired word length 3, so the
instantiated source bound 1 fits the target bound 4. At length 1 the paired length is 8 and
source bound 2 fits target bound 9. These are mathematical sanity calculations, not claimed
executable tests. The result remains class inequality at the positive normalization n + 1;
it claims neither direction of noninclusion. No statement strengthening or monotonicity
hypothesis is introduced.

## Executed evidence

- `Inventory.lean.txt`/`.out` inventories the target and its one compiler auxiliary. The target
  uses only `[propext, Classical.choice, Quot.sound]`; the auxiliary uses `[propext, Quot.sound]`.
  Its complete direct foreign-definition inventory is SPACE, NP, padLang and pairEncode.
- `Hierarchy-sealed.lean.txt`/`.out` is the full source with a local seal only around the new
  target section. All four foreign definitions are irreducible there. The four default-simp
  definition unfoldings actually present in this import closure (Action.apply, Cfg.init,
  MultiTapeTM.initCfg, **NDTM.initCfg**) are removed. It elaborates with zero errors and the one
  unchanged F6 admission warning. The earlier passing seal with defaults present is retained
  separately, not substituted for this stronger run.
- `Controls-unsealed.lean.txt`/`.out` contains four pointwise and four parameter-abstracted rfl
  equations; all eight close, exit 0. The identical goals with the seal produce exactly eight
  rfl failures and exit 1. `control-check.json` matches diagnostic source lines and
  multiplicities exactly, not merely a set of names. No unsafe reducibility option is used.
- `Census-*.out`, `AllConstants-*.out` and their deltas retain every compiled auxiliary in their
  respective non-private/all-constant populations, with kinds, module owners and visibility.
  The sole addition is the internal proof auxiliary above; nothing is removed or moved.
- Raw per-file policy/campaign lint is retained before/after. There is no new finding. No
  blueprint source or public-name binding changed; no strict blueprint claim is made here.

Every elaboration used leanelab, one process at a time, with the existing complete snapshot or
complete preflight overlay. No `lake build`, bare Lean invocation, cache operation, screen, Git
mutation, commit, push or actual proof-worktree source edit was performed by this reviewer.
`receipt.json` and per-run JSON files record inputs, paths, hashes, statuses and timings.
