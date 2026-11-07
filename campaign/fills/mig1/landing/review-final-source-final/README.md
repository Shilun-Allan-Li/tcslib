# Actual final source QA

**Not yet clear to merge.** Source fidelity passes at pushed head
`b1f553b315f31b949076e91119473ce4070e7d53`. The pending human API/home decisions, external gate and
fresh merged-tree replay remain separate. This review executed no Lean or screen and changed no
actual source or repository state.

`capture.json` freshly verifies the full API, producer, passed `0d6b6f84…` and phase 2 `429bdd59…`
commit objects and preserves twelve complete source snapshots at all five stages, including actual
final source. `final-head.json` independently verifies the final committed tree: all twelve committed,
actual and reviewed blobs are byte-identical; the working tree/index are clean; no untracked Lean
file exists. Both the API comparison and PR merge-base comparison change exactly the twelve owned
Lean files. The scope remains the original eleven plus the mechanical VirtualInput body repoint.

Relative to `429bdd59…`, only the private `fwdMapVirtual_run` proof and its leading sketch change.
The actual final Primitives blob is the passed inert candidate
`72226a291b0c7e9189883a0ebd75a88ca49bb1f19d0487e54316e542b847ee71`; the other eleven blobs are
identical to the immutable phase 2 capture. Both earlier frozen review folders passed checksum
verification. The final prototype preserves all 311 Primitives declarations, including 54 public
headers, without adding/removing a declaration.

## Contract and runtime preservation

The strict full-header comparison retains statement-local lets and proof-valued lets, verified by
four parser controls. All surviving public names, homes, visibility, kinds, literal headers, order,
complete attribute commands and annotations are preserved. Relative to API, the exact authored
public delta remains **three forwarding exports added and six Catalog exports retired**; final
adoption introduces no further public or private name/header/import/attribute delta.

Across all twelve files, the authored source census is **384→381 public, 1,080→766 private** from
API. VirtualInput contributes twenty unchanged public declarations to the earlier eleven-file
364→361 census; it publishes nothing new here. Full source counts are distinct from the compiled
namespace/materialization census, which the parent and independent metadata reviewer own.

The per-phase private accounting is unchanged: API has the three previously approved producer
strengthenings (`counter_count`, `loopHost_contracts`, `loopHost_prepare`); producer→repair has the
two Wrappers transport re-expressions (`timedReady_dispatch`, `timed_ledger`). Phase 2 adds four
private proof helpers and prunes two unused private selectors. The final adoption changes no
surviving private header and introduces no new helper.

All nine original private type/data/instance moves still match actual API Catalog originals modulo
the approved renames. All runtime/type/data bodies remain frozen except the two original authorized
private final `inj'` Prop proof fields, with complete headers, `toFun` and data prefixes byte-equal.
The gated forwarding wrapper body/theorem contracts and visible coefficients remain fixed.
All seventeen target admissions remain discharged; the exact three original RAM admission headers
and proof bodies remain frozen. These checks are recorded in `freeze-summary.json`, the four
comparison JSONs and `admissions.json`.

## Final roots and citation population

`proof-roots.json` and `.tsv` provide **144 roots: 66 public, 78 private**, with the exact same
name/owner/private/kind tuples as phase 2. The JSON additionally records current source lines,
body-end lines and literal header/body/declaration-chunk SHA256s plus normalized body-token hashes.
The root set remains 89 changed existing proofs plus 55 new/moved proofs relative to API.
`root-set-equivalence.json` states the body-hash method and pins the earlier list.

The complete source citation pass covers all 144 final bodies/headers and leading documentation,
with 2,390 resolved lexical entries, abbreviation expansion and uncertain candidates retained.
Its conservative TCSlib cited-home union remains **25 files**, with no new home relative to phase 2;
`screen-population-final-review.txt` is the complete list. No screen was run here. Existing Mathlib
invariant-reader homes and the bounded family enumeration remain in the preceding immutable route
and phase 2 records; no new family research occurred in this refresh.

All three unrestricted deterministic equal-time core tagged drivers now use the existing invariant
iterator: `bufferedSecondCfg_run`, `vhostEmitTM_runFrom`, and `fwdMapVirtual_run`. Their current body
hashes/lines are in `QA.json`. Richer nondeterministic word/liveness and variable-cost macro-time
variants remain separately disclosed; this is not a blanket all-TCSlib family retirement or debt
waiver. The scalar setup-induction exclusion remains distinct.

## Evidence boundary

The parent's final native process receipt is hash-linked in `QA.json`: exit 0, zero errors, 96.32 s
against its complete current4 context. Its input/output bytes were checked; full census, deltas,
descendants and axiom parsing are attributed to the independent metadata reviewer, not this review.
The parent also owns actual-tail compilation, final head screens and the fresh 394-module replay.
No earlier replay is relabeled as a final-tree replay here. The two on-demand compiler equation
materializations remain separately disclosed in the existing compiled accounting.

All twelve source hashes were stable through final QA. `MANIFEST.json` and `SHA256SUMS` freeze this
review. No source edit, Git mutation, cache/shared snapshot operation, Lean run, screen, commit,
push, dispatch, gate closure or merge clearance occurred in this review.
