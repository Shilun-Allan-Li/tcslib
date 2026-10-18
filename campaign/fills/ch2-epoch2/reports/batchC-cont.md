# Chapter 2 E2 continuation C — completed

Both inline machine obligations in `mem_NP_iff_exists_length_le` are filled.
The existing witness-equivalence proof and all semantic helpers are preserved.
Only `TCSlib/Complexity/ClassNP/NP.lean` changes. No remote push or PR was made.

## Provenance

- Repository: `https://github.com/Shilun-Allan-Li/tcslib`.
- Source branch: `complexity/arora-barak-ch1`.
- Required and actual code base: `64d82f84dfbbfcd7b5d69689dc0f37fb3d3116c4`.
- Working branch: `fill/ch2-e2cont-C`.
- Delivered commit: 7d343bfd9124cf44991e893a1e4108a2f22c15d4.
- Delivered tree: 5f284c073402c1f82b0304bf5410154c683066d9.
- Binding continuation brief read at branch tip
  `cc103db9d9f00e28924a685919629be9b3ec1b63`. That commit adds the briefs and
  planning updates; the code baseline is its parent, as the brief requires.
  The new local working branch was moved to that required base before edits.
  No other branch was changed.
- Lean `4.25.0`, release commit `cdd38ac5115bdeec5f609e9126cce00f51ae88b3`.
- Mathlib `029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e`.
- Single agent; no delegation.
- Final owned file: 679 lines, 32,936 bytes.

The original E2-C brief, predecessor report and continuation, policy/workflow,
infrastructure audit D5 and design §9c were read. The continuation brief controls
the narrower ownership, exact base, 57-module order, and absence of sanctioned
admissions for this target.

## Completed constructions

### Forward paired verifier

`pairedVerifier_mem_P` implements the aligned grammar guard, both length
inequalities, concatenation, and the old verifier. The upper bound is P8 at
`(C,c)`. For the reverse inequality, `verifier_poly_reverseBound` uses P5 to
generate `C(|x|+1)^c` trues, P3 to prepend one bit, and the audited general
pairing recipe to pair `u` with that word. P8 at `(1,1)` tests

```
C(|x|+1)^c + 1 ≤ |u| + 1  iff  C(|x|+1)^c ≤ |u|.
```

Conjoining the orientations yields exact width even when the coefficient or
degree is zero. The outer P6 grammar guard rejects malformed strings before
the old verifier runs.

`verifier_poly_pair` is the canonical §9c recipe:

```
H x = pairEncode (f x) []
s x = pairEncode x (H x)
t x = pairEncode (s x) (g x)
pairSnd (pairConcat (t x)) = pairEncode (f x) (g x).
```

The second threaded map uses `g ∘ pairFst` on the duplicated whole `s x`.
No payload-only map is treated as a cross-component operation.

### Reverse padded verifier

`paddedVerifier_mem_P` uses P10 at **`(C+1,c)`**, guards its empty failure
output, applies P9 to the valid threaded pair, guards marker failure, and
checks P8 at **`(C,c)`**. Only then does it run the supplied old paired
verifier on `pairEncode (y.take n) u`. The original prefix remains the head
throughout; the equation supplies `n ≤ |y|`, so that prefix has length `n`.
The last stage is the supplied language `V`'s decider on the pair, exactly as
the frozen `paddedVerifier` specifies; it does not apply the forward
exact-width predicate to this bounded witness.

The two new vocabulary bridges have these exact statements:

```lean
private lemma verifier_split_bridge (C c : ℕ) :
    solveSplit (C + 1) c = certificateSplit C c

private lemma verifier_strip_bridge :
    splitAtLastTrue = stripCertificate
```

The split bridge is definitional at the shifted coefficient. The strip bridge
uses the predecessor's complete last-true/all-false semantic specification.

### Runtime and capture discipline

All machines are obtained from the proved timed contracts, never from an
untimed computability theorem. `verifier_poly_cond` instantiates W3 and
dominates its three polynomials by their maximum degree. `verifier_poly_map`
uses C1 with an explicitly monotone polynomial and degree `c+1` to absorb the
input scan. Compositions use the proved `PolyTimeComputable.comp`.

`verifier_poly_indicator` deliberately runs the supplied old decider as W3's
test, with constant true/false branches. W3's finite controller is the capture
host; its proof consumes `capture_run`, including halting-transition output.
Thus the verifier run is captured and its singleton verdict is emitted by the
host. No new raw controller or duplicated capture invariant is needed.

## Library contracts consumed, by use

All `computesFunInTime_*` names below are in `Turing.FinTM`.

| Contract | Use |
|---|---|
| `computesFunInTime_const` | Empty payload in the pairing recipe, false rejection, and terminal Boolean outputs. |
| `computesFunInTime_cond` | Grammar, both width, marker, and original-bound gates; capture of the supplied old verifier. |
| `computesFunInTime_pairMapSnd` | Payload transformations in the exact `H/s/t` pairing assembly. |
| `computesFunInTime_pairDup` | Retain the whole request through that assembly. |
| `computesFunInTime_pairFst` | Extract the original input for polynomial generation; recover it inside the retained-request map. |
| `computesFunInTime_pairSnd` | Extract the old witness; final general-pairing extraction. |
| `computesFunInTime_pairConcat` | Complete general pairing and feed `x ++ u` to the forward verifier. |
| `computesFunInTime_pairValid` | Reject malformed original pairs, missing splits, and failed marker strips. |
| `computesFunInTime_polyUnary` | Exact unary original bound. |
| `computesFunInTime_prepend` | Add the one bit required by the reverse-comparison translation. |
| `computesFunInTime_pairLenCheck` | `(C,c)` original bound; `(1,1)` reverse exact-width orientation. |
| `computesFunInTime_splitSolve` | `(C+1,c)` split search. |
| `computesFunInTime_stripLast` | Strip the last marker only in a valid pair's payload. |
| `computesFunInTime_comp` | Consumed through `PolyTimeComputable.comp` for all sequential stages. |
| `Turing.capture_run` | Consumed by the proved W3 host instantiated in `verifier_poly_indicator` and the other guards. |

`mem_P_iff` supplies and repackages actual finite singleton-indicator deciders.
The existing pairing parser API is reused; no alternate encoding is introduced.

## Seven audited edge cases: machine-side discharge

| Edge case | Discharge point |
|---|---|
| `C = 0` | All catalog instantiations and both membership lemmas quantify over arbitrary natural coefficients. The reverse orientation is still exact, and the padded split uses `C+1`. The original-bound check accepts only the empty stripped witness. |
| `c = 0` | Unary generation and both P8 checks include zero degree; `verifier_poly_map` absorbs the scan with degree `c+1`. The shifted split bridge retains the predecessor's strict-monotonicity semantics at degree zero. |
| `x = []` | Extractors and P10 handle an empty pair head. The successful split branch proves `n ≤ |y|` and uses the exact `take` length, also at `n=0`. |
| `u = []` | General pairing and P9 retain a valid encoding even with an empty payload. Grammar guards distinguish this from the empty failure word. The reverse comparison's added bit also includes zero witness length. |
| All-false certificate region | P9 receives `pairEncode x v`, never bare `v`; `verifier_strip_bridge` turns the existing failure fact into `[]`, which the post-strip grammar guard rejects before consulting `V`. |
| Malformed strings / no split | The forward outer grammar guard rejects malformed encodings. In the reverse direction P10 failure produces `[]`; the pre-strip grammar guard rejects it. The `none` case of `paddedVerifier_mem_P` proves this for every failed search, including the empty input. |
| Marker after too many witness bits | After successful stripping, P8 at the original `(C,c)` checks the retained original prefix. The `¬hu` branch of `paddedVerifier_mem_P` proves rejection without consulting `V`, even when the witness fits the enlarged certificate region. |

These machine correctness proofs hold on every input, and the existing seven
semantic discharge families remain byte-identical.

## New private declarations

There are **20**, all in `Complexity`; no public declaration is added.

| Name | Role |
|---|---|
| `verifier_poly_linear` | Lift a linear timed contract into the polynomial normal form. |
| `verifier_poly_const` | Fixed output words. |
| `verifier_poly_cond` | Timed conditional closure and polynomial bound. |
| `verifier_fst` | Total first projection. |
| `verifier_snd` | Total second projection. |
| `verifier_concat` | Guarded pair concatenation. |
| `verifier_map` | Guarded payload map. |
| `verifier_poly_map` | Timed payload-map closure. |
| `verifier_poly_pair` | Audited general pairing assembly. |
| `verifier_split_bridge` | Shifted search vocabulary equality. |
| `verifier_strip_bridge` | Last-marker vocabulary equality. |
| `verifier_bound` | Original-bound Boolean test. |
| `verifier_poly_bound` | Its P8 timed realization. |
| `verifier_poly_indicator` | Captured old-verifier execution. |
| `verifier_mem_P` | Repackage the timed singleton indicator into `P`. |
| `verifier_poly_reverseBound` | Reverse exact-width comparison. |
| `pairedVerifier_mem_P` | First completed machine obligation. |
| `verifier_split` | Shifted threaded split function. |
| `verifier_strip` | Threaded marker-strip function. |
| `paddedVerifier_mem_P` | Second completed machine obligation. |

Requested shared lemmas / escalations: **none**. The existing owned file stays
below the policy's 1,000-line split threshold. Its 679 lines reflect preserving
the frozen semantic layer and keeping all new helpers private in the sole owned
file; a separate shared-API change is not needed for this batch.

## Verification

- Final fresh sweep: **57/57 modules pass; zero `error:` lines**. Each module
  passes the committed script's exit-status, error-diagnostic, and freshly
  produced-olean gates. The run uses a new isolated `.lake/e2cont-C-final`
  tree, not the development tree.
- The owned module plus all 16 later modules also passed sequentially before
  the final sweep. No owned-module diagnostics remain.
- Final sweep admission warnings: **27**, all in untouched out-of-scope
  declarations, versus 28 at the base. `NP.lean` has none.
- `mem_NP_iff_exists_length_le` prints exactly
  `[propext, Classical.choice, Quot.sound]`.
- Checked-kernel traversal of that target finds **no direct admission roots**.
  The traversal reads declaration types and values, including opaque values.
- A separate whole-module traversal covers **84 kernel declarations** originating
  in `NP.lean`, including generated declarations. Its transitive closure has no
  admission roots; every axiom set is contained in the standard triple. The
  program also checks all **20 new helpers** exist exactly once and are private,
  printing each helper's axioms.
- Statement freeze: **21 existing declarations** retain their ordered signatures
  and signature multiset; **3 public declarations** are unchanged with no public
  additions/removals. The stronger byte comparison reconstructs the exact base
  source by removing the new import and helper block and reverting only the two
  authorized proof-hole replacements. This also verifies all old docstrings,
  semantic proofs, and the surrounding equivalence proof are preserved.
- Style lint over ClassNP: **0 FAIL, 1 WARN**. The only warning is the unchanged
  1,206-line `TMSAT.lean`; the owned file has no warning (679 lines is an INFO
  against the 600-line target). No out-of-scope file was edited.
- `git diff --check` passes; exactly one tracked file changes; the working tree
  is clean after the local commit. The incremental bundle verifies against the
  required base. Patch replay on a separate index reproduces the delivered tree
  exactly, without checking out or modifying another branch.

Environment setup reused a same-pin local dependency cache and completed
`lake exe cache get` successfully (`cache-get.log`). An initial launch needed
this environment's existing Lean runtime-path compatibility shim; it failed
before the cache operation. The successful cache operation ran once, with no
files needing download. No `lake build` was run and no pinned configuration
was changed. An early bootstrap overlapped owned-module development and stopped
at a temporarily missing owned-module olean; the subsequent sequential downstream
pass and the final isolated fresh sweep above supersede that attempt.

The diagnostic is an acceptance check: any target or whole-module admission
root, or any axiom outside the standard triple, fails it. It does not whitelist
`sorryAx`. The remaining `enumMachine_contracts` root in untouched Chapter 2
files is outside this batch and is not consumed by this target.

### Final sweep tail

```
CHECK 55/57 TCSlib/Complexity/Formulas
RESULT 55/57 exit=0 seconds=1.096
CHECK 56/57 TCSlib/Complexity/CookLevin
RESULT 56/57 exit=0 seconds=1.221
CHECK 57/57 TCSlib/Complexity/ClassNP
RESULT 57/57 exit=0 seconds=1.351
SWEEP_PASS modules=57 seconds=175.791
UTC_END 2026-10-04T15:30:36.893986+00:00
```

## Flat archive and integration

The ZIP is flat: `SHA256SUMS`, this report, `NP.lean`, the format-patch series,
the incremental git bundle, final sweep and axiom logs, and supporting evidence
and reproduction programs are all root entries. Every payload other than
`SHA256SUMS` itself is hashed. `NP.lean` maps to
`TCSlib/Complexity/ClassNP/NP.lean` in the repository.

Verify with `sha256sum -c SHA256SUMS`. Apply the patch with `git am -3` on the
integration branch, or import the bundle, which requires the recorded base and
advertises only `refs/heads/fill/ch2-e2cont-C`. The source delta is exactly one
precise import, the new private helper block, and replacements of the two
authorized `sorry` terms; no existing statement, docstring, helper body, or
surrounding public proof structure changes.

For reproduction, put the pinned Lean on `PATH`, populate its pinned dependencies,
then run `TCSLIB_OLEANS="$PWD/.lake/e2cont-C-final" python3 /path/to/sweep.py "$PWD"`
and `bash /path/to/run-axioms.sh "$PWD"`. `check-freeze.py` takes the repository
path and compares against the exact recorded base.
