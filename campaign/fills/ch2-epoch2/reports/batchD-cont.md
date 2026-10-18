# Chapter 2 E2 continuation, batch D — completed fill

All three owned admission sites were discharged in the required order: **D-MEM → D-WRAP → D-EMIT**. `TMSAT_mem_NP`, `TMSAT_NPHard`, and the unchanged `TMSAT_NPComplete` assembly are admission-free. The quantitative bridge and polynomial time-constructibility theorem are also admission-free and unchanged. No continuation or statement escalation remains.

## Repository, base, and delivery

- Repository: https://github.com/Shilun-Allan-Li/tcslib
- Required base: `64d82f84dfbbfcd7b5d69689dc0f37fb3d3116c4`, on `complexity/arora-barak-ch1`.
- Working branch: `fill/ch2-e2cont-D`.
- Delivered commit: `45ea0842138ff6027465400ef6a8d3fc37839276`.
- Delivered tree: `79df844f3c5a6d18862ca594ce34e841fbdc2dbd`.
- Only changed repository path: `TCSlib/Complexity/ClassNP/TMSAT.lean`.
- Final source size: **1908 lines**; **46 new explicit private declarations**, zero new public declarations.
- Source SHA-256: `e3a0647bb89d5e7e074516bf08191463e925f438f2e2a2339995a2ac446fe5e0`.
- Delivery: `fill-ch2-e2cont-D.zip`, with every file at the archive root, including `SHA256SUMS`. The root-level `TMSAT.lean` belongs at the owned repository path above.
- Single-agent execution. No remote write, PR, push, or modification of another branch.

The fetched branch tip was `cc103db9d9f00e28924a685919629be9b3ec1b63`. Before source work, ancestry was checked and only the newly created working branch was pinned back to the brief’s required base. The original branch reference was preserved.

Binding records read: `briefs/ch2-e2cont-batchD.md`, the original E2-D brief, `audits/ch2-epoch2-agent-reports/batchD.md`, `workflow.md`, `policy.md`, the inherited E1-A pitfalls, the phase-3 resolutions, D5 in `audits/ch1-infra-r3-findings.md`, and the canonical recipe in `machine-library-design.md` §9c. The required 57-module order was used.

## Target and route accounting

| Site | Discharge |
|---|---|
| D-MEM | `tmsat_request_poly`, `tmsat_good_bounds`, and `tmsat_result_accept`, composed with the existing `tmsat_simulator_total`, `tmsat_simulation_budget`, and `tmsat_comp_on_image` in the filled local `hV`. |
| D-WRAP | Filled local `hwrap`: P6 `computesFunInTime_pairValid`; P13 `computesFunInTime_pairConcat`; timed captured composition with the supplied verifier; W3 `computesFunInTime_cond` with a fixed `[false]` branch. Coefficient and degree are enlarged to positive values only at the runtime level. |
| D-EMIT | `tmsat_certificate_unary`; the unchanged `poly_unary_computes` instantiated at loop parameter `2*e*r-1` and coefficient `D`; nested `tmsat_pt_pair`; P6 `computesFunInTime_pairEncodeFixed α₀`. |
| Completeness | Existing conjunction body unchanged; its two dependencies are now closed. |

### D5 residuals and canonical assembly

| Named obligation | Concrete discharge and library use |
|---|---|
| Exact odd split, rejecting even lengths | P10 `computesFunInTime_splitSolve 1 1`; `tmsatSplit`, `tmsat_split_some`, `tmsat_split_exists`, `tmsat_split_append`, and `tmsat_split_components`. A successful index solves `i + (i+1) = input.length`, so the split is unique. |
| Three nested quadruple parses | P6 `pairFst`/`pairSnd` contracts, `tmsat_pair_inverse`, `tmsat_pair_valid`, and `tmsat_good_spec`. `tmsatGood` short-circuits through the split validity and all three spine validities. `tmsat_pt_and` realizes the ordering with W3. Failure is never inferred from an empty extracted component. |
| All-true checks on both unary fields | P11 `computesFunInTime_incFixed` plus `computesFunInTime_ifEq []`; `tmsat_inc_nonempty`, `tmsat_inc_none`, and `tmsat_pt_unary`. This includes both empty unary fields. |
| Timed variable-prefix extraction | The actual finite machine `tmsatTakeTM`, with `tmsat_take_double`, `tmsat_take_separator`, `tmsat_take_parse`, `tmsat_take_payload`, and `tmsat_take_computes`. It emits exactly `b.take a.length` on `pairEncode a b`, within `(pairEncode a b).length + 1`. Its application in `tmsat_pt_take` is restricted to constructed pairs using `tmsat_comp_on_image`; no unproved totality claim on malformed inputs is needed. |
| Unary-to-binary clock conversion | P4 `computesFunInTime_lengthBits` is placed under C1 `computesFunInTime_pairMapSnd`. `tmsat_request_poly` first retains the entire request as the head and the clock as payload, maps the payload length counter, and extracts the resulting binary clock. C1 never reads the head. |
| General computed pairing | `tmsat_pt_pair` follows §9c literally: P14 duplication and C1 constant-empty map form `H`; P14/C1 form the retained-input `s`; a second P14/C1 stage applies `g ∘ pairFst` to form `t`; P13 concatenation and P6 second extraction give the required pair. The lemma is reused for prefix-machine inputs, clock retention, timed requests, and reduction emission. |
| Well-formed simulator request on every input | `tmsatRequest` and `tmsat_request_poly`; failed guards choose the fixed request with code `[]`, input `[]`, and deadline zero. |
| Relocated and captured simulation | Existing `tmsat_comp_on_image` uses the proved `bufferedComp_start` and `bufferedSecondCfg_run`. D-MEM supplies simulator totality only on the preprocessor’s image. D-WRAP uses the proved polynomial timed-composition calculus. |
| Success and timeout budget | Existing `tmsat_simulator_total` consumes both quantitative-bridge clauses. `tmsat_good_bounds` feeds the original input-length bounds to `tmsat_simulation_budget`; no monotonicity assumption about canonizer time is introduced. |
| Complete-answer recognition | `tmsat_pt_eq [true,true]` and `tmsat_result_accept`, using existing `tmsatAnswer_accept`. The whole captured answer is checked; timeout and every other completed output reject. |
| Invalid requests reject | `tmsat_result_accept` uses `FinTM.not_computesInTime_zero` for the fallback. The simulator is never assumed total on arbitrary malformed strings. |

### Completed predecessor obligation map

| Original obligation | Discharging lemmas / assembly |
|---|---|
| Concrete polynomial-value computation | Existing `polyUnaryTM`, `poly_loop`, `poly_start`, `poly_unary_computes`, `timeConstructible_poly`; unchanged. |
| Uniform concrete coefficient arithmetic | Existing `tmsat_serialization_length`, `tmsat_serialization_parameters`, `tmsat_concrete_coefficient`; unchanged. |
| Public quantitative bridge | Existing proved `timed_universal_quantitative`, from `Turing.timed_universal_concrete`; unchanged. |
| Both source outcomes | `tmsat_simulator_total`, integrated in the filled D-MEM body. |
| Full-output acceptance | `tmsatAnswer_accept` → `tmsat_result_accept` → `tmsat_pt_eq [true,true]`. |
| Explicit polynomial-canonizer chain | `tmsat_simulation_budget` → `tmsat_good_bounds` → the filled local simulator/composition budget. |
| Certificate bound and exact padding | Existing `tmsat_quad_bounds` and `tmsat_certificate_equiv`, unchanged; implemented prefix recovery is `tmsat_pt_take`. |
| Odd split and unique split position | Existing `tmsat_split_length` and certificate equivalence, plus the new checked P10 route above. |
| Quadruple parser and unary checks | `tmsat_fields_poly`, `tmsat_good_spec`, `tmsat_good_quad`, and the named D5 discharges above. |
| Binary clock conversion | The P4-under-C1 stage of `tmsat_request_poly`. |
| Relocation-and-capture | Existing `tmsat_comp_on_image` plus the proved library composition/branch contracts. |
| Total wrapper, including malformed input | Filled local `hwrap`, exactly realizing unchanged `tmsatWrapperOutput`. |
| Normalization and lawful fixed code | Existing `one_work_tape_binary`, `exists_codeTM`, and `decode_encode` chain in hardness; unchanged and now fed a proved wrapper. |
| Exact certificate value, all three cases | Existing `tmsat_exact_certificate_bits` retained; direct exact unary counterpart `tmsat_certificate_unary` uses the same case table. |
| Prescribed deadline majorization | Existing `tmsat_deadline_bound`, unchanged, with the exact `r`, `D`, and `T'` formulas below. |
| Exact binary deadline | Existing local `hdeadline` from `timeConstructible_poly D (2*e*r-1)` retained unchanged. |
| Fixed code, retained input, exact unary runs, and nested layout | Filled `hemit`, using `tmsat_pt_pair`, the unary generators, and P6 fixed-code pairing. |
| Component pinning and reduction correctness | Existing `tmsat_quad_injective` and `tmsat_reduction_correct`; unchanged. |
| Completeness | Existing `TMSAT_NPComplete` body; unchanged. |

## Exact-value discipline

The certificate output is always exactly `List.replicate (C₀*(input.length+1)^c₀) true`.

| Case | Emission |
|---|---|
| `C₀ = 0` | Finite-control constant `[]`. |
| `C₀ > 0`, `c₀ = 0` | Finite-control constant `List.replicate C₀ true`. |
| `C₀ > 0`, `c₀ > 0` | P5 `computesFunInTime_polyUnary C₀ (c₀-1+1)`, with the proved equality `c₀-1+1=c₀`. The harvested loop index is `c₀-1`. |

The deadline alone majorizes the normalized verifier runtime. Its formulas remain exactly:

```text
r  = max 1 c₀
D  = (K+1)*(B+1)^2*(C₀+3)^(2*e)
T' n = D*(n+1)^(2*e*r)
```

The original `hdeadline` and `hcertificate` binary witnesses remain unchanged. The authorized direct-unary route avoids converting those binary values back by countdown: the deadline uses `poly_unary_computes (2*e*r-1) D`, with `2*e*r-1+1=2*e*r`, and the certificate uses the case table above. Append-only implementation notes document this in the original target docstrings. **Neither copy of `polyUnaryTM` / `poly_unary_computes` was removed or modified.** No certificate length is majorized.

## Statement freeze, scope, and helper hygiene

`verify-freeze.py` compared nonempty, comment-stripped declaration bodies and signatures against the required base. Results:

- All **47 existing explicit declarations** remain in their original relative order, with identical signatures and visibility.
- Only the two intended theorem bodies, `TMSAT_mem_NP` and `TMSAT_NPHard`, changed.
- All other existing bodies, including every definition, the bridge, both in-file polynomial generator declarations, and the completeness theorem, are identical after comment stripping.
- Every original docstring’s contents remain verbatim; two append-only continuation notes explain the implementations.
- Exactly one precise import was added: `Build.Primitives`.
- No source admissions, new axioms, `unsafe` declarations, or public additions.
- `git diff --check` passed. Only the owned source path differs from the base.

The kernel-level inventory independently checks every declaration owned by the compiled TMSAT module, including generated descendants. It contains **325 declarations**; the union of their complete dependency traversals has no admission roots and only the standard axiom triple. Every non-private name belongs to an existing public declaration family. This is stronger than checking only the headline theorem closures.

The final size is **1908 lines**, under the brief’s inherited exclusive-file exception. The increase is the concrete prefix machine, runtime calculus, guarded parser semantics, and their proofs. Moving them to shared files would violate this batch’s ownership; any later extraction belongs to serial maintainer work. Style lint reports **0 FAIL, 1 WARN**, the owned file’s size. The linter’s declaration regex misses the unchanged `private noncomputable def` modifier order; the source inventory and kernel audit cover it.

### Every new explicit declaration

All names below are private in `Complexity`. Their source line numbers refer to the delivered full source. Generated declarations are exhaustively listed in `axiom-print.log`.

| Private declaration | Line | Role |
|---|---:|---|
| `tmsat_pt_linear` | 895 | Embed linear-time contracts in the polynomial-time calculus. |
| `tmsat_pt_const` | 902 | Obtain fixed-word emission from finite control. |
| `tmsatFst` | 906 | Total first projection with an explicit separate validity guard. |
| `tmsatSnd` | 909 | Total second projection with an explicit separate validity guard. |
| `tmsatConcat` | 912 | Name P13’s total pair-to-concatenation function. |
| `tmsatMap` | 916 | Name C1’s payload-only map. |
| `tmsat_pt_map` | 921 | Bound C1 by a monotone polynomial envelope. |
| `tmsat_pt_pair` | 944 | Prove the canonical §9c general pairing assembly. |
| `tmsat_pt_cond` | 966 | Embed W3’s captured branch in the polynomial calculus. |
| `tmsat_pt_eq` | 990 | Test equality with an entire fixed word. |
| `tmsat_inc_nonempty` | 998 | A successful fixed-width increment never returns an empty word. |
| `tmsat_inc_none` | 1004 | Overflow is equivalent to exact all-true shape. |
| `tmsat_pt_unary` | 1011 | Decide unary shape by P11 overflow and whole-word equality. |
| `tmsatTakeTM` | 1028 | Concrete one-work-tape, four-state counted native-prefix machine. |
| `tmsatTakeCfg` | 1052 | Indexed parser/payload configurations with the unary counter. |
| `tmsat_take_read` | 1058 | Identify the exact native input symbol. |
| `tmsat_take_double` | 1064 | Two equal prefix bits install exactly one unary counter cell. |
| `tmsat_take_separator` | 1096 | The separator enters payload mode at the counter’s final cell. |
| `tmsat_take_parse` | 1128 | Exact parser run and counter installation. |
| `tmsat_take_payload` | 1163 | Exact bounded native-payload emission invariant. |
| `tmsat_take_computes` | 1197 | Compute the requested prefix within encoded-input length plus one. |
| `tmsat_pt_take` | 1245 | Compose only on constructed pairs, using the actual output-length bound. |
| `tmsat_pt_and` | 1267 | Short-circuit conjunction of polynomial-time bit tests. |
| `tmsat_pair_inverse` | 1279 | Reconstruct a successful aligned parse. |
| `tmsat_pair_valid` | 1299 | Reconstruct the original word from guarded projections. |
| `tmsatSplit` | 1309 | P10 exact split at coefficient and degree one. |
| `tmsat_split_some` | 1315 | Every successful split satisfies the exact length equation. |
| `tmsat_split_exists` | 1322 | The unique solution is returned by the bounded search. |
| `tmsat_split_append` | 1334 | Recover an instance and its exact padded certificate. |
| `tmsat_split_components` | 1341 | Recover concatenation and the one-bit length difference. |
| `tmsatY` | 1356 | The recovered instance field. |
| `tmsatW` | 1359 | The recovered padded certificate. |
| `tmsatCode` | 1362 | The recovered machine code. |
| `tmsatInput` | 1365 | The recovered source input. |
| `tmsatWidth` | 1368 | The parsed unary certificate-length field. |
| `tmsatClock` | 1371 | The parsed unary deadline field. |
| `tmsatGood` | 1375 | Ordered grammar and exact unary-shape guards. |
| `tmsat_good_spec` | 1384 | Successful guards reconstruct the exact quadruple and split. |
| `tmsat_good_quad` | 1403 | Well-formed quadruples pass guards and recover every field literally. |
| `tmsat_fields_poly` | 1416 | Assemble the polynomial-time field and guard contracts. |
| `tmsatRequest` | 1437 | Valid simulator request, with a zero-deadline fallback. |
| `tmsatResult` | 1444 | Exact tagged simulator answer corresponding to preprocessing. |
| `tmsat_request_poly` | 1458 | Polynomial-time guarded request assembly and payload clock conversion. |
| `tmsat_good_bounds` | 1473 | Code length and deadline fit the original verifier-input length. |
| `tmsat_result_accept` | 1491 | Whole-answer equality is exactly the existential verifier language. |
| `tmsat_certificate_unary` | 1760 | Exact unary certificate emission by the binding three-case table. |

## Verification evidence

- Lean `leanprover/lean4:v4.25.0`; runtime commit `cdd38ac5115bdeec5f609e9126cce00f51ae88b3`.
- Mathlib `029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e`, checked against its checkout.
- `lake exe cache get` invoked once and completed successfully; `cache-setup.log` included. Pinned toolchain and dependency artifacts already present in the workspace were reused. Native launch uses an existing readlink compatibility shim for this execution environment; the compiler and its pin are unchanged.
- No manual `lake build` invocation. All source verification used `scripts/lean_check_tree.sh` and direct Lean for the axiom instrument.
- D-MEM was compiled closed before D-WRAP was filled; D-WRAP was compiled closed before D-EMIT was filled. Final owned-module compilation has no errors or warnings.
- Final authoritative sweep used a **separate fresh olean tree**: **57/57 ordered modules, exit 0, zero `error:` lines**. The check script removes the target olean and requires a freshly produced nonempty one for each module.
- **26 out-of-scope declaration admission warnings** remain in the campaign; **zero** in the owned module. Out-of-scope source files are byte-identical to the base.
- The final axiom instrument ran against that final fresh tree, not bootstrap artifacts. It checks headline prints, exact admission roots, all owned kernel declarations, all dependency axioms, and public visibility.
- Frozen-source and archive checks are independently rerunnable using the included scripts.

Exact headline prints and root reports:

```text
'Complexity.timeConstructible_poly' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.timed_universal_concrete' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.timed_universal_quantitative' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.TMSAT_mem_NP' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.TMSAT_NPHard' depends on axioms: [propext, Classical.choice, Quot.sound]
'Complexity.TMSAT_NPComplete' depends on axioms: [propext, Classical.choice, Quot.sound]
ROOTS Complexity.timeConstructible_poly: []
ROOTS Turing.timed_universal_concrete: []
ROOTS Complexity.timed_universal_quantitative: []
ROOTS Complexity.TMSAT_mem_NP: []
ROOTS Complexity.TMSAT_NPHard: []
ROOTS Complexity.TMSAT_NPComplete: []
```

Final sweep tail:

```text
CHECK 52 TCSlib/Complexity/TuringMachine
CHECK 53 TCSlib/Complexity/ClassP
CHECK 54 TCSlib/Complexity/Uncomputability
CHECK 55 TCSlib/Complexity/Formulas
CHECK 56 TCSlib/Complexity/CookLevin
CHECK 57 TCSlib/Complexity/ClassNP
FULL_SWEEP_PASS modules=57
```

## Archive and integration checks

The one format-patch is against the exact required base. The incremental bundle advertises only `refs/heads/fill/ch2-e2cont-D`, with the required base as its sole prerequisite. Bundle verification passed. Applying the patch to a temporary index initialized at that base reproduces the delivered commit’s entire tree. The root-level full source is byte-identical to the committed source. `package-validation.log` records these checks.

Apply `0001-ch2-e2cont-D.patch` using the maintainer’s normal integration process. With the pinned dependencies available and the branch name retained, `bash verify-lean.sh /path/to/patched/repo /path/to/output` reruns the fresh sweep, axiom audit, freeze check, and lint. The source checker deliberately enforces this batch’s working branch name; for integration on another branch, review that one branch guard separately rather than changing any source statement.

`SHA256SUMS` covers every archive payload except itself. All ZIP members are regular root-level files; no enclosing directory or nested source tree is needed. The archive includes the report, full source, patch, bundle, final sweep and axiom logs, source-freeze inventory, lint and environment records, package-validation evidence, cache log, summary, and reproduction scripts.

## Escalations and requested shared lemmas

None. All named D5 residuals and the three owned admissions are discharged. The fill is ready for maintainer integration and audit.
