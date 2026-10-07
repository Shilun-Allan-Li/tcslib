# Chapter 2, epoch 2, batch D — PARTIAL continuation delivery

**This is the partial-delivery case of ground rule 7, not a completed batch and not a closed audit gate.** `timeConstructible_poly` is fully proved. The other target bodies have checked assemblies, but membership and hardness retain three explicitly marked concrete-machine obligations. The mandated quantitative bridge is separately admitted under bridge-protocol step 3. There are **four explicit `sorry` sites in three declarations**. No private helper is admitted.

## Repository, base, and scope

- Repository: https://github.com/Shilun-Allan-Li/tcslib
- Required base branch: `complexity/arora-barak-ch1`.
- Base commit: `6c09453e6af59ff1575060b66196d28812800d24`.
- Working branch: `fill/ch2-e2-D`, created directly from that base as the committed brief instructs.
- Delivered commit: `7c91b03a3519d73159b6316f43e78d3812d77460`.
- Only changed repository path: `TCSlib/Complexity/ClassNP/TMSAT.lean`.
- No PR, push, checkout of `main`, or modification of another existing branch. Single agent; no delegation.
- The archive contains the complete modified source, one format-patch, and an incremental git bundle advertising `refs/heads/fill/ch2-e2-D`. The bundle requires the recorded base commit, which is its sole prerequisite.
- Existing declaration order and all five existing signatures are unchanged. The `TMSAT` definition is unchanged, even after comment stripping. No declaration was removed. The only deliberate new public declaration is `Complexity.timed_universal_quantitative`.

## Target status

| Target | Status | Exact frontier |
|---|---|---|
| `timeConstructible_poly` | **Proved, no `sorryAx`** | Concrete finite machine, exact output, and runtime bound checked. |
| `timed_universal_quantitative` | **Stated; bridge escalation** | One simulator before all codes and inputs; both success and timeout clauses; missing public concrete-simulator API described below. |
| `TMSAT_mem_NP` | **Partial** | Certificate equivalence, total timed answers, uniform polynomial budget, and buffered composition proved; `D-MEM` remains. |
| `TMSAT_NPHard` | **Partial** | Exact certificate-value cases, normalization, prescribed deadline, pairing pinning, and reduction correctness proved; `D-WRAP` and `D-EMIT` remain. |
| `TMSAT_NPComplete` | **Assembly filled, dependent on admissions** | The conjunction uses the two preceding targets. It is not an admission-free NP-completeness proof. |

Fill order was polynomial construction, bridge, membership, hardness, completeness. Out-of-scope admissions and source files were left untouched.

## Exact outstanding admissions

| Site | Current line | Remaining proof obligation |
|---|---:|---|
| `timed_universal_quantitative` | 636 | Bridge protocol step 3: expose the concrete bounded-answer theorem from Chapter 1, then use the proved coefficient estimate. |
| `TMSAT_mem_NP`, local `hV` / `D-MEM` | 943 | Build the odd-split/quadruple parser, unary-to-binary clock conversion, and well-formed timed-request preprocessor; assemble the verifier and its runtime. |
| `TMSAT_NPHard`, local `hwrap` / `D-WRAP` | 1131 | Build a total pair-to-concatenation wrapper, reject malformed pairs, and run the supplied verifier with a polynomial bound. |
| `TMSAT_NPHard`, local `hemit` / `D-EMIT` | 1169 | Retain the input while emitting the fixed code, doubled input, and the two exact unary runs; prove the nested pairing layout and polynomial runtime. |

The last three admissions are permitted **only because this is a partial delivery**. They are not covered by the bridge exception and must be removed before claiming a completed batch. The source marks them with `CONTINUATION D-MEM`, `D-WRAP`, and `D-EMIT` comments.

## Closed construction and proof-route deviation

The original polynomial time-constructibility sketch proposed binary schoolbook multiplication. This delivery instead constructs the exact unary value and composes it with the already-proved public binary length counter. The original sketch remains; an appended implementation note explicitly records this deviation. No statement or hypothesis changed.

The machine uses `c+1` unary loop tapes, each of side length `n+1`, and emits exactly `C` true bits per box point. Its full output is `List.replicate (C*(n+1)^(c+1)) true`. A recursive invariant preserves all outer heads and resets completed inner heads. A loop of depth `r` costs at most `(C+1+5*r)*(n+1)^r`; startup and the final halt give total budget `(C+5*(c+1)+4)*(n+1)^(c+1)`. Timed composition with `timeConstructible_id` emits the exact `Nat.bits` value within the required constant multiple of that value plus one. The theorem's domination condition uses `C>0`. The generator itself also handles `C=0`; the theorem does not assert time constructibility for that case.

This construction includes empty input and side length one. It does not cite private counter declarations from `TimeConstructible.lean`, use an assumed arithmetic machine, or introduce an axiom. The exact certificate-bit lemma separately follows the mandated three-way case split: zero coefficient, positive coefficient with degree zero, and positive coefficient with positive degree.

The file is 1185 lines. Its size warning is accepted for this delivery because the brief permits modification of only this file, and the first target needs the concrete machine and run invariants. Any shared-file extraction should occur serially at merge, not by changing frozen Chapter-1 sources in this batch.

## Bridge escalation: precise missing API

The **stated simulator bound** is

```text
(3 * α.length + 14 * c.canonizerTime α.length + 50) * (t + 1)^2.
```

`U` is quantified before `α`, the simulated input, and the deadline. The bound is a fixed closed expression in the code length and canonizer time, not a newly chosen coefficient per input. Both original `timed_universal` implications are present, including timeout rejection at deadline zero.

The public-API portion of the coefficient calculation **is proved**: `tmsat_serialization_length`, `tmsat_serialization_parameters`, and `tmsat_concrete_coefficient` show that the explicit startup-plus-block coefficient used in Chapter 1 is at most `3*|α| + 14*H + 50`, where `H = c.canonizerTime |α|`. This is not a proof that an arbitrary existential witness of `timed_universal` has that bound.

The missing fact is the concrete, uniformly selected simulator's bounded-answer theorem:

- `Universal.lean`'s `timedUniversalTM` is private.
- Its `timedStartupBound` is private.
- Its `timed_computes` theorem is private. It states that this concrete machine produces the exact `timedAnswer` within `(timedStartupBound c α + universalBlockBound c α + 14)*(t+1)^2`.
- `timedAnswer` is also private and can be exposed in an export statement by spelling out the source configuration at time `t`: `true :: output` if halted, `[false]` otherwise.

**Requested shared addition:** a public Chapter-1 theorem exposing this concrete bounded-answer guarantee with one simulator chosen before code and input, with the private startup expression expanded (or an equally strong explicit success-and-timeout theorem). The maintainer can then discharge this file's bridge by monotonicity and `tmsat_concrete_coefficient`. No Chapter-2 predicate, including `PolyBound`, belongs in that Chapter-1 addition. No private declaration from another source file is used as a proof dependency in this contribution.

This is the required bridge-protocol step-3 escalation. The bridge remains a genuine admission; neither the arithmetic lemma nor its two-clause statement is presented as a completed simulator construction.

## Obligation-to-lemma map

| Audited obligation | Discharging lemma or exact open frontier |
|---|---|
| Concrete polynomial-value computation | `polyUnaryTM`, `poly_loop`, `poly_start`, `poly_unary_computes`, and `timeConstructible_poly`; closed, with the documented route deviation. |
| Uniform concrete coefficient arithmetic | `tmsat_serialization_length`, `tmsat_serialization_parameters`, `tmsat_concrete_coefficient`; closed. Concrete simulator API remains at the bridge. |
| Both success and timeout clauses | `tmsat_simulator_total`; closed as a theorem with the bridge-shaped hypothesis. |
| Reject timeout or any non-`[true]` completed output | `tmsatAnswer_accept`; exact whole-answer semantics closed; machine integration remains in `D-MEM`. |
| Explicit `hc : PolyBound c.canonizerTime` budget chain | `tmsat_simulation_budget`, giving coefficient `3+14*C+50`, degree `max 1 e+2`; no monotonicity assumption on canonizer time. |
| Certificate length bounded by input length | `tmsat_quad_bounds`; closed. |
| Odd split and unique split position | `tmsat_split_length` and the `List.append_inj` step of `tmsat_certificate_equiv`; semantics closed; parser machine remains in `D-MEM`. |
| Quadruple parser and all-true unary checks | `D-MEM`, open. The existential verifier specification alone does not prove computability. |
| Exact certificate padding and prefix extraction | `tmsat_certificate_equiv`; closed. |
| Unary-to-binary clock conversion | `D-MEM`, open assembly obligation; public `timeConstructible_id` is available. |
| Relocation and capture | `tmsat_comp_on_image`; closed with budget `2*T₁(n)+T₂(n)+2`, assuming the second machine terminates only on the first machine's image. Concrete preprocessor integrations remain open. |
| Total wrapper including malformed pairs | `tmsatWrapperOutput` specifies the total function; `D-WRAP` must construct its machine. |
| One-work-tape normalization and fixed lawful code | The `one_work_tape_binary`, `exists_codeTM`, and `decode_encode` steps in `TMSAT_NPHard`, conditional on `D-WRAP`. |
| Exact certificate value, all three cases | `tmsat_exact_certificate_bits`, using `tmsat_constant_poly` and `timeConstructible_poly C₀ (c₀-1)`; closed. |
| Prescribed deadline majorization | `tmsat_deadline_bound`; closed with exactly `r=max 1 c₀`, `D=(K+1)(B+1)^2(C₀+3)^(2e)`, `T'(n)=D(n+1)^(2er)`. |
| Exact binary deadline | Local `hdeadline` in `TMSAT_NPHard`, via `timeConstructible_poly D (2er-1)` and proved positivity. |
| Fixed-code emission, doubled input, binary countdowns, nested tuple assembly | `D-EMIT`, open. Available exact bit-computation theorems do not substitute for these machines. |
| Pairing injectivity pins all components | `tmsat_quad_injective`; three explicit uses of `pairEncode_injective`, then unary lengths. |
| Reduction correctness and completed-output uniqueness | `tmsat_reduction_correct`; closed under the wrapper semantics hypothesis, instantiated in `TMSAT_NPHard`. |
| Completeness conjunction | `TMSAT_NPComplete`; body filled, dependent on the remaining admissions. |

## Every new explicit declaration

Public addition: `Complexity.timed_universal_quantitative`, the mandated bridge, at line 625.

All 41 declarations below are **private**. Each helper theorem is closed; the type, instances, and definitions contain no admissions. The full delivered module's compiler-generated declaration inventory is included in `logs/kernel-declarations.log`; source-level inventory and signature checks are in `logs/statement-freeze.json`.

| Private declaration (inside `Complexity`) | Line | Meaning |
|---|---:|---|
| `PolyControl` | 117 | Six families of finite controller states for copy/setup, nested loops, rewinds, advances, and fixed emission. |
| `polyControlFintype` | 125 | Private finite enumeration of the control type via its sum representation. |
| `polyControlDecidableEq` | 129 | Private decidable equality for the control type. |
| `polyTape` | 133 | A unary interval of true bits, blank outside the interval. |
| `polyMove` | 137 | A no-output action moving exactly one selected work head. |
| `polyUnaryTM` | 144 | Concrete finite binary machine enumerating a fixed-dimensional box and emitting the exact unary polynomial. |
| `polyCfg` | 174 | Canonical loop configurations with arbitrary outer heads and accumulated output. |
| `polyMove_apply` | 180 | A head-only action has exactly the stated single-head update. |
| `poly_emit` | 194 | The finite chain emits exactly its remaining number of true bits. |
| `poly_rewind` | 216 | Rewind restores the selected loop head to zero without changing other heads or output. |
| `poly_advance` | 249 | Returning to an outer loop increments exactly that loop head. |
| `polyCost` | 259 | Exact recursive cost of a full loop nest. |
| `poly_loop` | 271 | Full recursive loop invariant: exact output, exact cost, restored inner heads. |
| `polyTape_write` | 376 | Writing the first blank extends the unary tape by one cell. |
| `polyCost_le` | 389 | The loop cost is at most (C+1+5r) times the number of box points. |
| `polyCopyCfg` | 408 | Canonical configurations during the parallel unary-length copy. |
| `poly_copy` | 413 | An input scan copies the exact length to every loop tape. |
| `poly_setup` | 448 | Parallel startup rewind reaches the outermost loop at head zero. |
| `poly_start` | 472 | Startup installs side length |x|+1 in 2(|x|+1) steps. |
| `poly_unary_computes` | 506 | The exact unary polynomial is computed within (C+5(c+1)+4)(n+1)^(c+1). |
| `tmsat_serialization_length` | 639 | Canonizer output length is at most its time budget. |
| `tmsat_flatMap_length` | 645 | Flattening nonempty words does not shorten a list. |
| `tmsat_action_nonempty` | 655 | Every serialized transition record is nonempty. |
| `tmsat_serialization_parameters` | 670 | The serialization bounds the header bit length, initial index, and state count. |
| `tmsat_concrete_coefficient` | 703 | The concrete Chapter-1 coefficient expression is at most 3|α|+14H+50. |
| `tmsatAnswer` | 713 | The source deadline configuration determines a tagged full output or timeout. |
| `tmsat_simulator_total` | 723 | Both bridge clauses give total completed answers on well-formed requests. |
| `tmsatAnswer_accept` | 746 | Equality with the entire answer [true,true] is equivalent to source acceptance. |
| `tmsat_simulation_budget` | 760 | PolyBound on canonizer time gives a uniform polynomial simulation budget. |
| `tmsatQuad` | 788 | The exact right-nested quadruple encoding. |
| `tmsat_quad_bounds` | 792 | Each code/input/unary length fits in the quadruple length. |
| `tmsatVerifier` | 800 | Existential verifier specification with exact odd split and prefix extraction. |
| `tmsat_split_length` | 806 | The exact certificate convention forces odd total length and the unique split index. |
| `tmsat_certificate_equiv` | 818 | Padding and prefix extraction give exactly the original TMSAT witnesses. |
| `tmsat_comp_on_image` | 852 | Timed buffered composition assuming second-machine totality only on the first machine’s image. |
| `tmsat_deadline_bound` | 955 | The prescribed deadline formula majorizes normalized wrapper time. |
| `tmsat_constant_poly` | 990 | Finite-control constant emission gives a polynomial-time function. |
| `tmsat_exact_certificate_bits` | 1001 | Exact binary certificate generation in the prescribed three cases. |
| `tmsatWrapperOutput` | 1019 | Total mathematical wrapper specification; malformed pairs receive [false]. |
| `tmsat_quad_injective` | 1026 | Three pairing-injectivity steps pin all four components. |
| `tmsat_reduction_correct` | 1052 | A fixed wrapper with the prescribed accepting semantics gives exactly the source NP language. |

An initial visibility check caught that `deriving DecidableEq, Fintype` on a private inductive generated public instances. The final source uses explicitly private instances instead. The final kernel-level visibility check rejects any public declaration outside the five frozen declaration families and the mandated bridge family; it passed. Compiler-generated proof auxiliaries attached to the existing target theorems are listed in the kernel inventory.

## Verification evidence

- Lean: `leanprover/lean4:v4.25.0`, runtime commit `cdd38ac5115bdeec5f609e9126cce00f51ae88b3`.
- Mathlib: `029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e`, checked against the dependency checkout.
- Cache setup: successful `lake exe cache get` for the actual imported Mathlib modules; log included.
- Never invoked `lake build`. Iteration used the brief's direct-Lean script and direct scratch proof checks.
- Final authoritative sweep: **53/53 modules, exit 0, zero `error:` lines**, using a separate fresh olean tree after the visibility repair. Each module's script removes its old olean and requires a fresh result.
- Sweep admission warnings: **31 declarations** total, including three declarations in this owned file. The remaining warnings are unchanged out-of-scope declarations. Four source `sorry` sites here yield three declaration warnings because hardness contains two local admissions.
- All 41 explicit private declarations: axiom subsets of `[propext, Classical.choice, Quot.sound]`, **no `sorryAx`**.
- `timeConstructible_poly`: `[propext, Classical.choice, Quot.sound]`, **no `sorryAx`**.
- Bridge and all three TMSAT targets: standard axioms plus `sorryAx`, as expected for this partial delivery.
- A transitive constant-dependency traversal checks the precise admission roots; it does not infer them merely from source warning counts.
- Frozen signature/order/definition comparison: PASS. New public source declaration: bridge only. No removals. `git diff --check`: PASS.
- Style lint: zero FAIL; the file-size warning is justified above. The existing lint regex misses the `private noncomputable def` modifier order and therefore reports one fewer private declaration; the source inventory and kernel audit check all 41 explicitly.

Final sweep tail:

```text
CHECK 49 TCSlib/Complexity/ClassP
CHECK 50 TCSlib/Complexity/Uncomputability
CHECK 51 TCSlib/Complexity/Formulas
CHECK 52 TCSlib/Complexity/CookLevin
CHECK 53 TCSlib/Complexity/ClassNP
FULL_SWEEP_PASS modules=53
```

Axiom admission roots:

| Declaration | Direct/transitive `sorry` roots |
|---|---|
| `timeConstructible_poly` | none |
| `timed_universal_quantitative` | itself |
| `TMSAT_mem_NP` | itself (`D-MEM`), bridge |
| `TMSAT_NPHard` | itself (`D-WRAP`, `D-EMIT`) |
| `TMSAT_NPComplete` | membership, hardness, bridge |

Thus the bridge-only admission condition for a **completed** batch is not yet met. This report explicitly invokes the brief's partial-delivery continuation provision. No nonstandard axiom other than these listed admissions appears.

## Continuation and archive checks

Continue by discharging `D-MEM`, then `D-WRAP`, then `D-EMIT`, while the maintainer handles the Chapter-1 bridge addition serially. The marked goals already specify the total functions and exact formulas required. Do not replace exact certificate lengths with majorants or assume the simulator terminates on malformed requests.

`SHA256SUMS` covers every archive payload except the checksum file itself. `logs/package-validation.log` records bundle verification, application of the patch to a temporary index initialized at the base, and equality of the reconstructed tree with the delivered commit. The source in the archive is byte-identical to that commit. `verification/verify-lean.sh` reruns the full sweep and axiom audit from a repository with the patch applied; `verification/verify-freeze.py` reruns the source freeze and scope checks against the pinned base.
