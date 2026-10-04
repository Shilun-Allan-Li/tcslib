# Batch P4 — machine-library closure

**Complete.** `computesFunInTime_splitSolve` is proved by a concrete finite body and the existing `splitSolve_of_body` / `exists_loopFindTM` route. There are no remaining admissions in the owned file or anywhere in `Build/`. No continuation frontier remains.

## Base, branch, and ownership

- Repository: `https://github.com/Shilun-Allan-Li/tcslib`.
- Required and actual base: `494d48353d292cca5d90675f5421f1bce09068e3`.
- Working branch: `fill/lib-P4`, created directly from that exact base on `complexity/arora-barak-ch1`.
- The P4 brief was read from branch head `23c04aba994ae8239b502b08cd915183971b1294` before selecting its required base. The four binding documents, P3 frontier, policy, workflow, and relevant audit findings were read before implementation.
- Only `TCSlib/Complexity/TuringMachine/Build/Primitives.lean` is changed in the commit. Verification programs and delivery files are outside the repository diff.
- Delivery commit: 67bdd83f7258f1230fc9976eb0424f26449916fe.
- Final source size: 4418 lines. The P4 brief explicitly retains the existing file-size exception and requires helpers to remain in this owned file; the additional phase proofs follow that rule. No code was moved elsewhere.
- No push or pull request was made; no other local branch was modified.

## Ten-step work-plan discharge

| Step | Discharging construction or lemma | What is checked |
|---|---|---|
| 1 | `SplitBodyState`, `splitBodyTM`, private finite/equality instances | A finite controller with disjoint anchor, preparation, counting, decision, rewind, restoration, and emission phases; candidate on tape zero. |
| 2 | `splitBody_start` | The genuine initial configuration is literally the empty-candidate `Cfg.ofWords` anchor seam. Startup time zero is justified by that equation. |
| 3 | `splitEmbed_cut`, `splitBody_prepare`, `splitBank` | First-return embedding and a field-by-field dispatch seam: native head, overflow flag, candidate/source tape order, unary side length, zero heads, empty physical output. |
| 4 | `splitBody_count`, `splitSource_poly`, `splitSource_constant` | Exact table agreement for counted simulation through the first source halt, including an emitting final transition. Positive exponent uses the existing generator at depth `e`; exponent zero uses `catalogPrefixTM` on empty virtual input. |
| 5 | `splitBody_round`, `splitBody_rewind`, `splitRewindTM` | The check uses both blank native input and the no-overflow flag via `splitCount_accept`; the Boolean verdict is retained during a proved native-input rewind. |
| 6 | `splitEmitTM`, `splitEmit_double`, `splitEmit_separator`, `splitEmit_suffix`, `splitEmit_run` | The new accepting emitter reads **native-input bits** and uses candidate cells only as a length counter. It outputs exactly the doubled native prefix, `[false, true]`, and the native suffix in `s.length + w.length + 3` steps. |
| 7 | `splitBody_restore`, rejection branch of `splitBody_round` | Dispatch is identified with `splitRestoreScan … 0`. Existing exact restoration is reused, followed by one explicit transition to the anchor. Scratch is blank, all heads are home, and output is empty. |
| 8 | `splitSafe`, `splitSafe_add`, `splitSafe_one`, `splitSafe_join`, `splitBody_round` | Safe traces compose through **every** phase. The initial anchor departure takes one step; the rejecting anchor return is the final step. Every strict interior time excludes the anchor, and round duration is positive on both branches. |
| 9 | `splitBody_envelope` | Counts source time plus all scans, dispatches, rewind, emission, and cleanup. Uses the original length-only invariant, including the one-past-end state. |
| 10 | `splitSolve_source`, `splitSolve_closed`, public `computesFunInTime_splitSolve` proof | Instantiates the constructed body in both exponent cases, supplies both missing body hypotheses, and applies the existing audited loop closure. All axiom-program expectations are empty. |

The accepting and rejecting branches are both formal Lean proofs. There is no remaining conditional body-existence assumption in the public theorem: `splitSolve_source`'s exact source hypothesis is discharged by `splitSource_constant` or `splitSource_poly` in the public proof.

### Round and time details

For source duration `T`, the full round proof gives a positive duration at most

`T + 5 * s.length + 3 * w.length + 20`.

The actual accepting emitter takes `s.length + w.length + 3` steps. Its tape-zero bit values never supply output symbols. All earlier preparation, counted evaluation, checking, and rewind transitions are physically silent, so output begins only after acceptance is established.

The common body coefficient is

`A = (C + 1 + 5 * e) * 2 ^ e + 40`.

The bound uses `s.length + 1 ≤ 2 * (w.length + 1)` and the existing `catalogPolyCost_le`. It does not increase the required body exponent `e + 1`; `splitSolve_of_body` supplies the final exponent `e + 2` and enlarges the coefficient to cover the existing binary length/fuel machine.

The invariant remains exactly `s.length ≤ w.length + 1`. No all-true restriction was added. At the one-past-end state, acceptance is impossible; the existing restoration component returns the **same arbitrary-bit word**, silently and in positive time. The checked combined trace proves the anchor guard on that stall too.

### Loop-hypothesis mapping

- `hF`: the existing `computesFunInTime_lengthBits` witness, with its coefficient enlarged inside `splitSolve_of_body`.
- `hInv0`: the existing empty-word length proof in `splitSolve_of_body`.
- `hInvStep`: unchanged `splitStep_inv`.
- `hstart`: `splitBody_start`, with the proved zero-time witness.
- `hround`: `splitBody_round`, acceptance-length simplification, and `splitBody_envelope`.
- Search, failure, payload, and final exponent: unchanged `splitStep_orbit`, `splitFind_eq`, `splitFind_none`, `splitLoop_result`, and `splitLoop_bound`, reused through the existing closure.

## Freeze and verification

- Final fresh sweep: **57/57 modules passed; 0 errors; 0 Build admission warnings**. Exactly 28 unchanged out-of-scope campaign admission warnings remain.
- All **23 library contracts** print at most `[propext, Classical.choice, Quot.sound]`; every expected root set is empty.
- Whole-`Build` traversal: **1,171 checked declarations; no admission roots; no nonstandard axioms**.
- Source freeze: all **153 existing declarations** retained in order; all **15 public source declarations** and their signatures preserved; all **153 original docstrings** retained verbatim. Only the target proof body changes.
- Kernel export freeze against a separately compiled exact baseline: **78 public kernel declarations preserved**, no removed declarations, and **187 added private declarations**, including the 29 named helpers and compiler-generated descendants.
- Style lint: **0 FAIL, 2 WARN**. Warnings are the already-excepted `Loop.lean` size and the explicitly permitted owned-file size.
- `git diff --check`, bundle verification, and patch application check against a temporary index at the exact base all pass.

Final sweep log tail:

```text
MODULE 54/57 TCSlib/Complexity/Uncomputability
MODULE 55/57 TCSlib/Complexity/Formulas
MODULE 56/57 TCSlib/Complexity/CookLevin
MODULE 57/57 TCSlib/Complexity/ClassNP
SWEEP_PASS modules=57
```

The mechanical freeze check compares existing declaration order, the public declaration multiset and order, complete old declaration bodies except the target proof, the target's exact signature, and all old docstrings. It records no removed or added public declarations and no changed existing helper. All historical status/spec docstrings remain verbatim; a new closure note records the final state.

The whole-`Build` traversal checks kernel declarations, types, opaque bodies, and constructor dependencies. It also checks the axioms of every declaration in all four `Build` modules, so unused helpers are covered. Every expected admission-root set for all 23 contracts is `[]`. All 29 new named private declarations have separate axiom reports. Compiler-generated descendants are covered by the whole-tree traversal and the private-export check.

A first export check detected that `deriving DecidableEq` generated a public instance for the private control type. That intermediate version was not delivered. The final code uses an explicitly private equality instance, and the final traversal checks that the new implementation declarations and their descendants are private. The exponent-case proof is also packaged in private `splitSolve_closed`, so the public target introduces no generated public proof helper. A separately compiled baseline inventory confirms that the complete public kernel-declaration set is unchanged.

Requested shared lemmas: **none**. Statement/realizability escalations: **none**. No frozen statement was weakened, restated, renamed, or altered. Target 14 and all previous proofs are unchanged.

## New private declarations

- `splitSafe`
- `splitSafe_add`
- `splitEmbed_cut`
- `splitRewindTM`
- `splitEmitTM`
- `SplitBodyState`
- `splitBodyStateFintype`
- `splitBodyStateDecidableEq`
- `splitBodyTM`
- `splitBank`
- `splitBody_start`
- `splitEmbed_run`
- `splitBody_prepare`
- `splitBody_count`
- `splitBody_rewind`
- `splitBody_restore`
- `splitEmitCfg`
- `splitEmit_double`
- `splitEmit_separator`
- `splitEmit_suffix`
- `splitEmit_run`
- `splitSafe_one`
- `splitSafe_join`
- `splitBody_round`
- `splitSource_poly`
- `splitSource_constant`
- `splitBody_envelope`
- `splitSolve_source`
- `splitSolve_closed`

These are the 29 explicitly named implementation declarations. `SplitBodyState` also generates private constructors/recursors and related declarations; definition compilation generates private equation/proof helpers. `new-kernel-privates.txt` records all newly added checked names, and `build-declarations.tsv` records the complete checked `Build` inventory.

## Environment and reproduction

- Lean 4.25.0, compiler commit `cdd38ac5115bdeec5f609e9126cce00f51ae88b3`.
- Mathlib `029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e`; the repository manifest and toolchain file are unchanged.
- Exactly one `lake exe cache get` invocation was made. It built the cache executable but returned status 1 without a completion message on this host. Cache setup was completed by running that executable through `lake env`; the successful cache log is included. No project `lake build` was run.
- The host required the supplied `proc_self_compat.c` shim: it maps only the current process's `/proc/<pid>/exe` readlink to `/proc/self/exe`. It does not change Lean code, proof terms, or kernel verification. Ordinary hosts should not need it.
- Bootstrap checked the first 25 modules, and the owned module plus all 31 later modules were checked after implementation. The final gate is a separate full 57-module sweep into a fresh olean tree.

From the repository at the exact base, either apply the included patch with `git am` on `fill/lib-P4`, or recover the branch commit from the bundle. `Primitives.lean` is the complete source for the owned destination path above; it is also provided for inspection. The archive contains only root-level members.

With the pinned compiler on `PATH` and the pinned dependency cache available:

```bash
python3 /path/to/extracted/sweep.py --repo . --oleans /tmp/p4-fresh-oleans
P4_KERNEL_INVENTORY=/tmp/p4-build-declarations.tsv \
  python3 /path/to/extracted/run_axioms.py --repo . --oleans /tmp/p4-fresh-oleans
python3 /path/to/extracted/freeze.py --repo .
python3 scripts/style_lint.py TCSlib/Complexity/TuringMachine/Build
```

`PrimitiveAxioms.lean` must be beside `run_axioms.py`, as it is in the archive. `SHA256SUMS` lists every other archive member; verify with `sha256sum -c SHA256SUMS` after extraction. The bundle has the exact required base as its prerequisite.

Notation: `w` is native input; `s` is the candidate word; `C` and `e` are the frozen polynomial parameters; `T` is source duration; `A` is the common body-time coefficient. Other names are existing or listed Lean declarations.
