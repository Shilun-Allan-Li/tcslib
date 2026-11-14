# Final3 explicit-list manual review

Status: COMPLETE. All 595 rows have individual completed dispositions;
pending rows: 0. No Lean or Lake process was run for this review.

The native inventory contains **four foreign-definition candidate items** and
15 lexically open items. All four candidate items invoke the registered
`reduceIte` metaprogram as a simplifier procedure. They do not request a
foreign object-level definition body. The reviewed count of new foreign
definition **body readings** is therefore 0. The raw candidate count remains 4
in the JSON and is not suppressed or relabeled as a raw zero.

## Input and source binding

| Evidence | SHA-256 |
|---|---|
| `final-scan-plan.json` | `5a2301b66d344357afdbc6173db92d5c0255baad1d034ea67058109217ebcffa` |
| `final-explicit-scan.json` | `20d91fdecac9604dfb6e94bf82779d30bc385d519ecc4facb24de0ba4d18cbec` |
| `snapshot.json` | `eff1943af135d87490fdd993b25f18b5eea0944eb71d0de195227fa2b4065112` |

`final-explicit-manual-review.json` retains every original row's source path,
line, declaration, item, NEW/CHANGED/SAME status, original native resolution,
candidate identities, and completed manual disposition. It also records the
native raw-log path/hash, draft path/hash, and exact reviewed hashes of the
eight owned/provider files. The materializer checks those hashes against both
the frozen source snapshot and current proof source before producing a review.

The runnable materializer is `evidence/tools/manual_explicit_review_final3.py`;
the saving command was
`python3 -I evidence/tools/manual_explicit_review_final3.py --write`.
The earlier source review and its explicit row maps remain in the final3 draft
and in `evidence/tools/manual_explicit_review_draft.py`. Final1 and final2 evidence remain unchanged. The saving command writes the
complete JSON and supporting source excerpts directly.


The entire **104-module** import-closure snapshot was verified against both
its frozen source copies and the current checkout. The complete path/hash map
is retained as `reviewed_import_closure_source_hashes` in the JSON; all eight
owner/provider hashes also appear separately. The native probe source and
its delivered source copy are checked against the plan's probe-source hash.
The proof commit is `fa33b9b8fa3a9b801a7db8857d7a2739c61c1e16`.

## Completed dispositions

| Disposition | Rows |
|---|---:|
| Native-confirmed same-file definitions in SAME declarations | 36 |
| Individually identified local equation proofs | 66 |
| Native-confirmed named equation/contract theorems | 468 |
| Inline typed equation proof | 1 |
| Registered metaprogram simplifier entries | 4 |
| Individually identified local lets | 8 |
| Native-confirmed published theorems through dot notation | 12 |
| Total | 595 |

There are 383 NEW rows, 4 CHANGED rows, and 208 SAME rows. Every selected
global constant has its exact native name, kind, and home recorded. All
definition-kind selections are either one of the 36 definitions whose native
home equals the occurrence's own file, or one of the four metaprogram entries
individually reviewed below. No other Core, Mathlib, or TCSlib definition-kind
selection was silently cleared.

## Four actual foreign-definition candidates

The native identity for each of these four rows is:

```text
name: reduceIte
kind: def
home: Lean.Meta.Tactic.Simp.BuiltinSimprocs.Core
source item: ↓reduceIte
```

| Row | Proof location | Individual disposition |
|---:|---|---|
| 216 | `Algebra.lean:124`, `unitCollision_extract` | In the false/true-selector case, use the registered procedure to select the now-known conditional branch before `one_mul`. |
| 219 | `Algebra.lean:126`, `unitCollision_extract` | In the true/false-selector case, select the conditional branch in the collision hypothesis and goal; no declaration body is used as a rewrite rule. |
| 483 | `FromDiscreteLog.lean:279`, `dlHashEval_expF` | In the false-selector case, simplify the proved false conditional before applying the unit-power value reader. |
| 486 | `FromDiscreteLog.lean:281`, `dlHashEval_expF` | In the true-selector case, simplify the proved true conditional before the multiplication/value readers. |

This is supported by the exact pinned Lean 4.25.0 sources copied as numbered
excerpts in `explicit-simproc-source-evidence.json`:

| Toolchain source | Whole-file SHA-256 | Reviewed lines |
|---|---|---|
| `/Users/seyoonr/.elan/toolchains/leanprover--lean4---v4.25.0/src/lean/Lean/Meta/Tactic/Simp/BuiltinSimprocs/Core.lean` | `afb764e9ab1bd7750115c1c9e839f2f148f2052f76cecc9168ca1b0b64a0a884` | 10–25 |
| `/Users/seyoonr/.elan/toolchains/leanprover--lean4---v4.25.0/src/lean/Lean/Elab/Tactic/Simp.lean` | `531b17f323f416d0b53b3874681d707b65c3d4dec7814ee54c04aa0fda58f360` | 94–128, 250–266, 333–344 |

`Core.lean` registers `reduceIte` using `builtin_simproc`. It constructs
conditional-equation proofs with `ite_cond_eq_true` or `ite_cond_eq_false`.
The elaborator identifies registered procedures through `isSimproc?` or
`isBuiltinSimproc`, returns `.simproc`, then `.addSimproc`, and adds the
procedure to the simplifier's procedure set. This takes a different elaborator
branch from `.expr` followed by `elabDeclToUnfoldOrTheorem`. Thus the four source
items call proof-producing tactic machinery; they do not ask `simp` to unfold
the metaprogram definition into the mathematical expression being proved.
No Rule 10 exception or object-definition unfolding is inferred from the
constant's `def` kind alone.

## Fifteen scanner-open items

All 15 have original native resolution `UNRESOLVED`; there are no ambiguous
items in this inventory. The original values remain in each JSON row under
`native_resolution`, while the manual dispositions are complete.

| Row | Source token and location | Source binding or proof supplier |
|---:|---|---|
| 2 | `ha`, provider line 158 | First-numeral length equality from `obtain` in `WellFormedIndex.dlW_eq`. |
| 4 | `ha`, provider line 164 | First-numeral length equality from the `WellFormedIndex.length_eq` obtain pattern. |
| 5 | `hb`, provider line 164 | Second-numeral length equality from that same obtain pattern. |
| 6 | `hc`, provider line 164 | Third-numeral length equality from that same obtain pattern. |
| 114 | `show ... from (hs z).2`, provider line 722 | Typed equality proof supplied by the locally returned public block-rejection host contract; `show` is syntax. |
| 115 | `he`, provider line 727 | Branch equation `g z = []` supplied by `split_ifs with he`. |
| 130 | `hvdef`, provider line 775 | Local equation introduced by `set v := ... with hvdef`. |
| 131 | `hs`, provider line 775 | None-branch sampler equation introduced by `rcases hs : sampleBelowL ...`. |
| 133 | `hvdef`, provider line 777 | The same local `set` equation, used in the some branch. |
| 134 | `hs`, provider line 777 | Some-branch sampler equation introduced by the same `rcases`. |
| 343 | `he`, `Reduction.lean:206` | Index-representation equality obtained through public `wellFormedIndex_iff`. |
| 424 | `hs`, owned line 152 | None-branch sampler equation from `cases hs : sampleBelowL ...`. |
| 427 | `hs`, owned line 154 | Some-branch sampler equation from the same `cases`. |
| 455 | `he`, owned line 220 | Index-representation equality from the `wellFormedIndex_iff` obtain pattern. |
| 539 | `hkey`, owned line 498 | Generated-key equality obtained from public `dlHashGenFun_key`. |

Every occurrence uses the identified proof term as an equation. Definition
symbols inside the type of an inline proof are not themselves unfolding
requests. These scope explanations were checked against the frozen source
copies, not inferred from absence of native candidates.

## Other corrected lexical classifications

Rows 153 and 197 denote native theorem `ZMod.val_natCast`; row 488 denotes
native theorem `ZMod.val_mul`. Both exact names have home
`Mathlib.Data.ZMod.Basic`. The scanner's local-name heuristic falsely captured
the type name `ZMod` as a binder. Their selected native theorem identities are
explicitly restored in the final JSON.

Rows 398, 437, 446, 457, 477, 480, 491, 494, 540, 568, 580, and 588 use
`hw.dlW_eq` with `hw : WellFormedIndex n i`. The native table confirms the exact
published theorem
`TCSlib.Cryptography.Candidates.WellFormedIndex.dlW_eq`, home
`TCSlib.Cryptography.Candidates.DiscreteLog`, kind `theorem`. These are
dot-notation applications of its width equation rather than local-member body
reads.

The eight local-let occurrences are only the proof-local `width`, `u`, and
sampler-result `w`, identified individually in the JSON. The other 66 local
records are equality proofs. All 36 native definitions used as body readers
are same-file occurrences in declarations classified SAME against the issue
base. Whole-file seals independently test implicit foreign TCSlib dependency
reads; this explicit-list review does not replace their results.

## Repaired declarations and remapped occurrences

The complete revised `collisionPost_split`, `dlHash_compresses`, and
`dlHash_collision_accept_eq` proofs were inspected. They are the only three
declaration code hashes that differ from final2. The final3 draft records the
old/new hashes and the exact occurrence mapping; final3 native candidates were
checked afresh rather than inferred from the old review.

In `collisionPost_split`, rows 360–365 now prove only the natural-number
`hwidth` equality using the same six local/public reader items. Whole-value
`congrArg (fun k : ℕ => List.ofFn (padFin k raw))` then composes with the exact
published padding-word reader. No dependent simplification needs the body of
`padFin`.

The two owned proofs apply key/value/field readers first and dimension readers
second. Their reader multisets are unchanged; 15 occurrences are reordered.
The JSON retains both old and new row IDs for these items. The dot-notation
`hw.dlW_eq` occurrence formerly at final2 row 573 is final3 row 568. Every
remapped global exactly matches its expected fully qualified name, kind, and
home in the fresh final3 native table. No additional explicit foreign body
reading was introduced by the staging changes.

The final3 Reduction source hash is
`27e4d37dc581ff2db70336b8b19ce3a92531de09c0e42ff260a9ffd4685b04c6`;
the owned-module hash is
`9d500a96e0e112a092ec0f2e548c5a648752dba89faa4bee40272ef55fcf78d0`.
Other owner/provider source hashes are unchanged. This review concerns explicit
lists and source identity; all final3 kernel, axiom, sweep, seal, and control
results remain separate required evidence.
