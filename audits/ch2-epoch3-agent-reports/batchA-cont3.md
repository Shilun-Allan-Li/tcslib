# A3 padding-cluster delivery

All five requested targets are closed, in the order **1, 6, 3, 4, 5**.
The banked sixth campaign headline `NEXP_subset_iUnion_NTIME` remains unchanged.
No shared-lemma requests or mathematical escalations are required.

## Repository and provenance

- Repository: `https://github.com/Shilun-Allan-Li/tcslib`.
- Required source branch: `complexity/arora-barak-ch1`.
- Working branch: `fill/ch2-e3cont-A3`; no push or PR.
- Object-verified required base: `f57cf9c1f0835a2336b93a61c6a6e4c9b1b266f0`.
- Source branch tip observed during setup: `61cf595831e920854f4f047796478a8913ad90a1`.
  The required base is an ancestor of that tip; the new work branch starts
  at the required base. The original branch ref is unchanged.
- Delivery commit: `d8196cf636175dc53df15645c08c7d9ab8e5e086` (tree `7fdbcc369047f11e30b41e552dbc090abcd44356`).
- Brief-path discrepancy: the exact requested path `briefs/ch2-e3cont-A3.md`
  is absent on the source branch. The committed
  `briefs/ch2-e3cont-batchA3.md` explicitly names this task, work branch,
  base, and delivery. It was read first, the discrepancy was disclosed,
  and its required pin and instructions govern this delivery. Its exact
  branch-tip contents are included as `continuation-brief.md` because the
  brief itself is not present at the earlier required pin.
- All cited predecessor briefs, the three predecessor reports, and
  `audits/emitter-fill-resolutions.md` were read. The current brief resolves
  the A2 ordering escalation by requiring target 6 before target 4.

## Closed targets and audited routes

| Order | Target | Discharging route |
|---|---|---|
| 1 | `ntime_expPow_subset_NEXP` | Public `computesFunInTime_splitSolveWith`, unchanged `e3_exp_bits_timed`, and unchanged `e3_verifier_of_split`. |
| 2 (target 6) | `EXP_subset_NEXP` | Private binary evaluator, public exponential split search, explicit failure rejection, installed captured decider, exact padded certificates. |
| 3 | `NEXP_eq_iUnion_NTIME` | Antisymmetry of the two proved inclusions. |
| 4 | `EXP_eq_NEXP_of_P_eq_NP` | Exact padded language in NP through the bounded paired interface, then A2 countdown emission and timed buffered execution of its polynomial decider. |
| 5 | `P_ne_NP_of_EXP_ne_NEXP` | Contraposition of target 4. |

### Split-recovery seams

Target 1 instantiates the public split search at
`f n = a * 2 ^ ((n + 1) ^ c)`, with evaluator budget
`B * (n + 1) ^ (c + 1)`. Its monotonicity is proved directly.
The in-body alignment unfolds `e3Split` and `solveSplitWith`, using
`Bool.beq_eq_decide_eq`; this is the requested one-unfold alignment, with
no new statement or axiom. Its final bound is
`D * (B * 2 ^ (c + 1) + 2) * (n + 1) ^ (c + 2)`.
The admitted target's old proof-body scaffolding was replaced; all proved
predecessor helpers remain byte-for-byte identical.

Target 6's `a3_exp_bits_timed` privately re-derives the `e3ShiftTM` template
in `EXP.lean`, under the section-8 harvest rule. The originals are unchanged.
`a3_split_timed` applies the same public search; its final use has coefficient
one. `a3_split_strictMono` proves strictness of the sum, including constant
width at exponent zero. `a3_split_complete`, `a3_split_none_iff`, and
`a3_split_empty` supply uniqueness, exhaustive rejection, and the empty-input
case. `a3NonemptyTM` explicitly rejects the empty failure payload.

`a3_decider_clean` consumes `exists_installCallTM`, including its positive
tape-count witness. The native loader copies and rewinds the input. A
dedicated first action handles entry-equals-exit; only an actual first
positive return permits singleton extraction. `a3_source_budget` charges
the captured source at the recovered prefix length, where its exponential
deadline is linear in the padded length. `a3_comp_at` accounts for the real
intermediate word instead of passing a coarse majorant to an exponential
source deadline.

### Theorem 2.22 seams

Here `E(n) = C * 2 ^ ((n + 1) ^ c)` is the exact certificate width.

`a3nVerifier` first parses the outer pair and then its first component.
Malformed outer and inner pairs reject. `a3n_pair_inverse` reconstructs the
original paired input in the reverse equivalence.

`a3n_verifier_mem_P` uses unconditional `e3_exp_bits_timed` on the parsed
original input, before either length check. Polynomial-time projections and
composition establish its budget on every input. The retained evidence
lemma `a3n_prevalidation` independently records the substring length bound
and the polynomial bound on the binary width's length; it does not assume
accepted padding. No post-validation logarithmic bound budgets evaluation.

Two full-word binary comparisons enforce `pad.length = E(x.length)` and
`u.length = E(x.length)` separately; `a3n_poly_unary` enforces the all-true
shape. `a3n_pad_eq` combines shape and the first exact length. The native
comparator checks complete words, including the final blank, so neither a
prefix nor an extension can pass. The outer bounded witness requirement
replaces neither exact equality. The verifier then assembles `x ++ u` and
runs the polynomial verifier through the timed polynomial catalog.

`a3n_pad_mem_NP` uses exactly the required reverse direction of
`mem_NP_iff_exists_length_le`, at parameters one and one.
`a3n_pad_emit` retains the original input and uses **A2's
`a2_exp_scheduler`**, hence its proved binary evaluator and countdown
(`a2_countdown` / `a2_decode_computes`), to emit exactly one true per debit
in a single emission phase. A payload map and input duplication preserve
`x` while constructing the exact pair; no nondeterministic-machine route
is used. `a3n_unpad_EXP` executes the padded-language decider at the actual
pair length. `a3n_scaled_envelope` includes the encoded-input factor-three
rescaling and absorbs all small lengths and zero parameters via unchanged
`a2_exponent_bound`.

## Preservation and sizes

`verify-preservation.py` removes only the two new private blocks and the
three flagged A3 docstring appendices, verifies each target signature, and
restores just the five target proof bodies from the base. The result is
**exactly equal to the pinned source files**. Thus all pre-existing
signatures, definitions, proved bodies, imports, options, attribution, and
docstrings remain unchanged, including all 133 designated predecessor
privates and every other existing private. Only the two owned files differ.

| File | Final lines | Final bytes | Existing privates preserved | New privates |
|---|---:|---:|---:|---:|
| `TCSlib/Complexity/ClassNP/EXP.lean` | 3252 | 168403 | 115 | 35 |
| `TCSlib/Complexity/ClassNP/Nondeterminism.lean` | 5835 | 301637 | 235 | 36 |

The brief's recorded size exceptions apply; splitting files would violate
ownership and frozen-private requirements. The mechanical style check has
zero failures and only these two expected size warnings. Every new
nontrivial proof has a local English sketch. No new public declaration,
axiom, admission, unsafe definition, or trust workaround was added.

## New private declarations

### EXP.lean (35 declarations)

- `a3_bits_shift`
- `a3ShiftTM`
- `a3_shift_scan`
- `a3_shift_computes`
- `a3_shift_timed`
- `a3_exp_bits_timed`
- `a3RunTM`
- `a3LoadCfg`
- `a3_copy_step`
- `a3_copy_run`
- `a3_load_rewind`
- `a3_run_start`
- `a3_run_guarded`
- `a3_run_call`
- `a3_run_singleton`
- `a3_decider_clean`
- `a3_comp_at`
- `a3NonemptyTM`
- `a3_nonempty_run`
- `a3_nonempty_nil`
- `a3_nonempty_computes`
- `a3_split_strictMono`
- `a3_split_unique`
- `a3Split`
- `a3_split_spec`
- `a3_split_none_iff`
- `a3_split_complete`
- `a3_split_empty`
- `a3SplitWord`
- `a3_split_length`
- `a3_split_timed`
- `a3Verifier`
- `a3_verifier_append`
- `a3_source_budget`
- `a3_verifier_mem_P`

### Nondeterminism.lean (36 declarations)

- `a3n_poly_linear`
- `a3n_poly_const`
- `a3n_poly_cond`
- `a3n_fst`
- `a3n_snd`
- `a3n_concat`
- `a3n_map`
- `a3n_poly_map`
- `a3n_poly_pair`
- `a3n_comp_at`
- `a3nEqTM`
- `a3nEqCfg`
- `a3n_eq_double`
- `a3n_eq_separator`
- `a3n_eq_parse`
- `a3n_eq_rewind`
- `a3n_eq_scan`
- `a3n_eq_end`
- `a3n_eq_compare`
- `a3n_eq_computes`
- `a3n_poly_eq`
- `a3n_poly_fixed_eq`
- `a3n_inc_nonempty`
- `a3n_inc_none`
- `a3n_poly_unary`
- `a3n_pair_inverse`
- `a3nVerifier`
- `a3n_pad_eq`
- `a3n_verifier_mem_P`
- `a3nPadLanguage`
- `a3n_pad_member`
- `a3n_pad_mem_NP`
- `a3n_prevalidation`
- `a3n_scaled_envelope`
- `a3n_pad_emit`
- `a3n_unpad_EXP`

## Environment and verification

- Lean 4.25.0, commit `cdd38ac5115bdeec5f609e9126cce00f51ae88b3`.
- Mathlib `029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e`.
- `lake exe cache get` was invoked once. It failed fetching the ProofWidgets
  cloud release; `cache-get.log` preserves that result. An already available
  local dependency cache was copied into this checkout. All eleven installed
  package source revisions match the committed manifest and their tracked
  sources are clean; `dependency-pins.json` records them. Optional documentation
  packages are absent and are not needed for the 57-module campaign.
- The available pinned Lean installation was reused. The runtime needed the
  included `proc_exe.c` adapter: its sole interception rewrites a readlink of
  `/proc/<own-pid>/exe` to `/proc/self/exe`. It does not alter Lean, source,
  generated proof terms, or kernel checking. Reproduction can compile it with
  `cc -shared -fPIC proc_exe.c -o proc_exe.so -ldl` and set `LD_PRELOAD` if the
  same environment requires it; ordinary environments do not need it.
- No `lake build` was run. Direct checks use the campaign's committed
  `scripts/lean_check_tree.sh`, as required by the binding continuation brief.
- Bootstrap and owned-plus-later checks preceded final verification.
- The final full sweep ran into a previously absent tree and passed all 57
  modules in the committed order, producing 57 fresh nonempty `.olean` files
  with zero `error:` diagnostics. It began at the base commit with the final
  source changes in the working tree; `source-SHA256SUMS` and
  `verification-summary.json` pin exactly that verified source snapshot.
  The snapshot was rechecked unchanged before delivery. The log ends:

  ```text
  CHECK 55 TCSlib/Complexity/Formulas
  PASS 55 TCSlib/Complexity/Formulas
  CHECK 56 TCSlib/Complexity/CookLevin
  PASS 56 TCSlib/Complexity/CookLevin
  CHECK 57 TCSlib/Complexity/ClassNP
  PASS 57 TCSlib/Complexity/ClassNP
  FULL_SWEEP_COMPLETE modules=57 time=2026-10-06T00:33:11Z
  ```
- Kernel traversal on the final fresh tree passed for all six campaign
  headlines, twelve epoch-2 targets, twelve library/emitter regression
  declarations, and all 71 new source helpers (226 checked kernel
  declarations including generated auxiliaries). Every audited closure has
  empty admission roots and axioms contained in the standard triple. The
  audit independently confirms exactly the seven out-of-scope direct
  admission roots. Headline axiom prints are:

```text
'Complexity.ntime_expPow_subset_NEXP' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.EXP_subset_NEXP' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.NEXP_eq_iUnion_NTIME' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.EXP_eq_NEXP_of_P_eq_NP' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.P_ne_NP_of_EXP_ne_NEXP' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.NEXP_subset_iUnion_NTIME' depends on axioms: [propext, Classical.choice, Quot.sound]
```
- `git diff --check` passed; only the two owned files differ. The work
  branch is clean. The incremental bundle verifies successfully and names
  exactly `refs/heads/fill/ch2-e3cont-A3` at the delivery commit, with the
  required base as its prerequisite. Applying the format patch to a detached
  worktree at the exact base reproduces tree `7fdbcc369047f11e30b41e552dbc090abcd44356`.
  The original source branch ref remains unchanged; nothing was pushed.

## Reproduction

1. Fetch the specified repository and exact source branch. Verify the base
   object above, then create an isolated work branch at that pin.
2. Apply the included patch with `git am 0001-close-padding-cluster.patch`.
   Alternatively, fetch `fill/ch2-e3cont-A3` from the included incremental
   bundle into an isolated local ref; the bundle requires the base history.
3. Select the pinned toolchain and manifest dependencies, with mathlib's
   compiled cache available. The included environment adapter is needed only
   under the same executable-resolution restriction.
4. Run `bash run-full-sweep.sh /absolute/repo /absolute/new-olean-tree` from
   the extracted audit directory. The tree must not exist initially. Capture
   the log and require exit zero plus `FULL_SWEEP_COMPLETE modules=57`.
5. Run `bash run-axiom-audit.sh /absolute/repo /absolute/new-olean-tree`.
   The runner includes only that fresh project tree and dependency libraries
   on `LEAN_PATH`; it excludes old project build trees.
6. Run `python3 verify-preservation.py /absolute/repo` and `git diff --check`.
   Check the flat archive's manifest with `sha256sum -c SHA256SUMS`.

## Delivery

The archive is flat: every member, including `SHA256SUMS`, is at its root.
It contains this report, both complete modified sources, the patch series,
the incremental git bundle, final sweep and axiom logs, preservation and
style logs, the audit/reproduction programs, provenance records, and checksums.
`SHA256SUMS` covers every member except itself. Full source names map to
`TCSlib/Complexity/ClassNP/EXP.lean` and
`TCSlib/Complexity/ClassNP/Nondeterminism.lean` in the repository.

Requested shared lemmas / escalations: **none**. All requested targets are
closed; no continuation frontier remains.
