# §12 F2 / continuation A2 — complete, 2 of 2

Both remaining targets are proved. `Catalog.lean` checks with **zero error diagnostics and zero sorry warnings**, completing the §12 routine layer's 56 statements. The final facade check also passes. There is no remaining frontier and no admitted new helper.

## Repository, order, and frozen scope

- Repository: `https://github.com/Shilun-Allan-Li/tcslib`.
- Required starting branch: `complexity/arora-barak-ch3-4` (not `main`).
- Recorded base: `3099ad2a4da95f0560bb6bd5ed54d3fcecd73ed9`.
- Working/delivery branch: `fill/s12-f2-A2`.
- First commit, loop ledger: `35a96f2c9598541d9260b87911f7e98c513f0bdb`.
- Second commit, forwarding controller / delivery HEAD: `ed8819661a78c1c9a50da95bfd65ffa93b4cde12`.
- Only changed tracked path: `TCSlib/Complexity/TuringMachine/Build/Catalog.lean`.
- The loop target was completed and checked before work on the forwarding controller. Patch order records this order.
- No push, PR, rebase, or `lake build` was performed.

All 378 existing declarations retain their order, signatures, docstrings, imports, options, and non-target bodies, including all F1 material and the 306 F2A private helpers. Only the two original `sorry` bodies and 45 new private source declarations differ. Removing those new helper blocks and restoring the two original bodies reconstructs the base file **byte for byte**; see `verification/owned-file-audit.json` and the included audit script. No public declaration was added, removed, or restated. No existing docstring appendix was added or changed; historical “fill pending” wording remains frozen.

The report at `audits/routine-f1-agent-reports/batchF2A-REPORT.md`, both briefs, the infrastructure/F1 resolutions, and their binding audit obligations supplied the proof routes below.

## 1. `Turing.FinTM.exists_loopTM_spaceUsed` — PROVED

The round-1 Part-2 assessment row states:

> **Supported, same host family.** The old orbit test through indices `0,…,R(n)` retains its time clause and obtains all-time work space `c(S(n)+T(n)+1)`. Actual startup/round windows are within `T(n)`, restart body heads at the origin, and either return silently or halt with the singleton verdict; their accumulated visited sets fit fixed origin-centred intervals. The fuel word has length at most `T(n)`, and the attached host reuses its counter/capture tapes. A more explicit space derivation appears in answer 5 below.

Witness: the existing private host `f2_loopHost body F anchor false`. The received `f2_loopHost_contracts` and the private segment summation `a2_loop_halted_run` establish the unchanged orbit-test function and time clause. If `c₀` is the received time coefficient and `k` is this host's tape count, the theorem chooses **`c = c₀ + 19*k`**.

For `n = x.length` and `ℓ = (Nat.bits (R n)).length`, every host head is bounded at every time by the fixed radius

`B = S n + 4*ℓ + 8`.

Taking inclusive visited-set cardinalities gives

`space ≤ k*(2*B+1) = k*(2*S n + 8*ℓ + 17) ≤ 19*k*(S n + T n + 1) ≤ c*(S n + T n + 1)`.

The number of rounds never multiplies this radius or its cardinality. It appears only in the required time bound `c*(T n+1)*(R n+2)`.

### Six-step binding ledger

| Answer-5 step | Discharged by | Proof obligation and bound |
|---|---|---|
| 1. Actual source windows | `a2_loop_start_prefix`, `a2_loop_round`, `a2_call_prefix`; target's `hlocal` | Startup prefixes are within the supplied startup endpoint; returning rounds use their supplied endpoint; accepting rounds use the first actual halt. Each endpoint is at most `T n`, so precisely the supplied budgeted source-space hypotheses apply. |
| 2. Origin-based interval union | `a2_source_radius`, `a2_call_run`, `a2_call_heads`, `a2_segments` | The unit-step walk contains the interval between zero and its endpoint in its visited set. A total-space bound `S n` therefore bounds each source head by `[-S n,S n]`. Captured calls project those source heads. The same fixed common interval is reused across all calls and all halted tails, rather than summing round footprints. |
| 3. Fuel source and retained bank | `a2_fuel_heads`, `a2_loop_prepare`, `a2_call_heads` | Fuel prefixes use `hFspace`. Preparation returns the actual fuel endpoint together with its `S n` head bound; subsequent call configurations retain that same fuel configuration. |
| 4. Fixed-width counters | received `f2_loop_fuel_width`, `f2_loopDebit_iterate_length`, `f2_loopHost_fuel_setup`, `f2_loopHost_reject`; `a2_loop_prepare`, `a2_loop_round` | `ℓ ≤ T n`. Fuel installation costs `3*ℓ+4` bounded work steps; its potentially long native-input rewind leaves work heads unchanged via `f2_rewind_heads`. Debits preserve the word length, including final underflow. A round's stop/debit administration is bounded by `2*ℓ+5`, with fixed acceptance allowances. |
| 5. No accumulating output log | `a2_call_prefix`, `a2_loop_start_prefix`, `a2_loop_round` | Append-only output makes every prefix of a silent startup/rejection silent. An accepting endpoint has exactly `[true]`, so capture length is at most one. The retained phase contracts rewind/reuse the capture bank between calls. |
| 6. Flag, boundaries, cardinalities | `a2_call_heads`, `a2_heads_steps`, `a2_heads_join`, `a2_segments`; received `f2_space_radius`; target's `hall` | The flag head is zero in each captured-call projection. Fixed controller movements are covered by the common radius `S n+4*ℓ+8`. Its interval cardinality is summed over the fixed tape count, then `ℓ ≤ T n` is applied. |

The assembled proof deliberately uses a conservative common interval: width-bounded administrative segments enlarge a phase's radius by their duration. This is a fixed allowance around each canonical call, not an allowance accumulated from round to round. The source/fuel projection lemmas supply the sharper source bounds within calls, and the existing phase endpoints reset the administrative starting positions.

The helper `a2_loop_halted_run` is a private copy of the received decision-segment summation in `Build/Loop.lean`. It does not introduce a new loop machine. The scope remains the decision export; no space theorem for the configuration/result-bearing siblings is claimed.

## 2. `Turing.FinTM.computesFunInTime_pairMapSnd_spaceUsed` — PROVED

The matching round-1 assessment states:

> **Supported as an existential target, but not by the documented old witness (R4).** It retains the original linear-plus-`Tg` time and adds `Sg(n)+c(n+1)` space, assuming monotonicity of both budgets and all-time payload space. A controller can first validate and buffer the pair, output the encoded first component, and simulate `Mg` on a buffered second component while forwarding its output. Source work-head trajectories remain unchanged, giving coefficient 1 on `Sg`, and the input buffer/administration costs only `O(n+1)`; this construction must replace the capture-all-output sketch.

The round-2 R4 ledger further requires:

> The payload work bank starts blank with heads at zero; administrative stages leave those heads stationary. During simulation its head positions are exactly source positions, possibly repeated during controller microsteps. After payload halt, the host freezes those heads. Hence the payload bank's contribution is at most `Sg |b|`, with coefficient **one**, at every horizon.

Witness: **`a2_mapTM Mg true`**, the commissioned new forwarding controller. It has two input-buffer tapes plus exactly `Mg.k` source tapes. It does not use the captured-output `pairMapTM` witness. The auxiliary `a2_mapTM Mg false` freezes at its live payload entry and serves only to certify the first arrival at that seam; the theorem's witness always uses forwarding mode.

### Named construction obligations

| Stage or obligation | Declarations | Established behavior |
|---|---|---|
| Finite control and physical action table | `a2_MapState`, `a2_mapStateFintype`, `a2_mapAct`, `a2_mapTM` | Parse a doubled prefix and delimiter; buffer both input components; rewind buffers; emit the encoded prefix; simulate the payload. Administrative actions leave every payload tape blank with its head at zero. |
| Validating buffer stage | `a2_map_first`, `a2_map_block`, `a2_map_suffix`, `a2_map_parse` | Recognize the exact `pairDecode` grammar, buffer the decoded first component and complete suffix, and reject malformed encodings with empty output. |
| Buffer rewinds, including empty buffers | `a2_map_backB`, `a2_map_backA`, `a2_map_finish` | Left overshoot and right entry establish the virtual input at position zero of its buffer and the first-component emission at its beginning. The empty-list cases are in the proofs. |
| Encoded-prefix emission | `a2_map_emit` | Emit doubled bits of `a` followed by `01`, in `2*|a|+2` steps; the prefix is exactly `pairEncode a []`. |
| Complete setup bound | `a2_map_setup` | From the genuine initial configuration, reach a valid payload seam or a silent malformed-input halt in at most `5*(n+1)` steps. |
| Seam and unchanged source origins | `a2_mapEntered`, `a2_mapSetup_stationary`, `a2_mapSetup_step`, `a2_mapSetup_run`, `a2_mapSetup_head_step`, `a2_mapSetup_heads`, `a2_map_launch` | Choose the first live payload entry, identify its entire configuration, transfer every pre-entry prefix to the real witness, and keep source heads zero throughout setup. |
| Both virtual-input boundary clamps | `a2_mapVirtual`, `a2_mapVirtual_step`, `a2_mapVirtual_run` | The second buffer is read at source input position minus one. `virtualMove_correct` proves the left and right clamps and tag update for every virtual input, including empty `b`. No nonempty-input premise appears. Each payload source step takes exactly one host step. |
| Forwarded output and final emission | `a2_mapVirtual_step`, `a2_mapVirtual_run` | The source action's output is the physical host action's output. Host output equals `pairEncode a [] ++ source.output`; no work tape stores forwarded output. The last halting action and all stationary post-halt times are included. |
| Malformed rejection and its tail | `a2_map_reject`; target's `none` branches | The real witness agrees with setup at every time, halts silently by the setup bound, and freezes thereafter. Payload heads remain at their source origins. |
| Coefficient-one source containment | `a2_map_space`; target's local `hp` in each decode branch | For each payload tape and host horizon `t`, the host visited set is a subset of the source visited set through horizon `t`: setup positions map to source time zero; later positions map to source time `v-u ≤ t`. Sum the source cardinalities once, with no tape-count multiplier on `Sg`. |
| Administrative and halted-tail bounds | target's `hshort`, `ha`, `hb`, `hrun` | Before the seam, unit-step movement over at most `5*(n+1)` steps bounds both buffers. Afterwards the first-buffer head is fixed at `|a|`, and the second-buffer head lies in `[-1,|b|]`, including after source halt. |

The configuration/read/action helpers `a2_mapCfg`, `a2_mapCfg_read`, and `a2_map_move` support the exact setup traces. `a2_mapSumEquiv` and `a2_map_sum` are private copies of the existing finite-sum splitting facts, needed before their later in-file counterparts are available.

### R4 constants and unchanged time clause

Let `n = x.length`, and on a valid input let `pairDecode x = some (a,b)`. Put `D = 5*(n+1)` and let `u` be the first payload-entry time.

- `u ≤ 5*(n+1)` and every payload source step takes one host step, so completion occurs by `u + Tg |b| ≤ 5*(n+1+Tg |b|) ≤ 5*(n+1+Tg n)`.
- Both buffer visited sets lie in `[-D,D]`. Their combined contribution is at most `2*(2*D+1) = 20*(n+1)+2 ≤ 22*(n+1)`.
- Payload tape containment gives `space ≤ Sg |b| + 22*(n+1) ≤ Sg n + 22*(n+1)`. The second inequality uses `hSg` and `|b| ≤ n`.
- On malformed input, the source bank is idle at zero; its origin contribution is bounded by `hgs x t`. The same `22*(n+1)` administrative allowance covers validation and the halted tail.

Thus R4 permits `A=22`, `B=5`, and the theorem uses the **single constant `c=22`** for both conjuncts. The original function, failure result `[]`, hypotheses, and time expression `c*(n+1+Tg n)` are unchanged.

## Verification

- Pinned Lean: `leanprover/lean4:v4.25.0`.
- Pinned mathlib: `029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e`; manifest unchanged.
- Ran `lake exe cache get`; all 7506 requested cache files were obtained and decompressed.
- Completed the prescribed 65-module bootstrap, inserting `Build/Embed`, `Build/Seam`, `Build/Catalog`, `NDCodes`, `Formulas/QBF`, and `Formulas/QBFEncoding` before the facade. The supplemental bootstrap log records all 71 checks as PASS. Its earlier Catalog snapshot still had the original admissions; final evidence is in `final-sweep.log`.
- Final Catalog check: exit 0, fresh `.olean`, zero errors, zero sorry warnings.
- Final `TCSlib/Complexity/TuringMachine` facade check: exit 0, fresh `.olean`, zero errors, zero sorry warnings.
- Both required axiom prints, and all 17 inherited F2 target prints, are exactly `[propext, Classical.choice, Quot.sound]`. None contains `sorryAx`. See `axioms.log` and `verification/axioms.lean`.
- Frozen-text reconstruction, declaration inventory/order, imports/options/docstrings, and exclusive-file audit: PASS.
- `git diff --check`: PASS.
- Scoped campaign style checker: **0 FAIL, 1 WARN**. The warning is the 10,876-line file; the brief explicitly forbids splitting it and freezes all received material. The new controller and local proof interfaces account for the growth. No public helper surface was added.
- Both patches replay against the recorded base in a temporary index and reconstruct the exact delivery tree `2c662672134a93b4a6f60f812532b035cc1fe416`.
- Git bundle verification: PASS; it requires the recorded base commit.

Final sweep log tail:

```text
PASS TCSlib/Complexity/TuringMachine/Build/Catalog: exit=0; errors=0; sorry_warnings=0; fresh_olean=yes

$ bash scripts/lean_check_tree.sh TCSlib/Complexity/TuringMachine
PASS TCSlib/Complexity/TuringMachine: exit=0; errors=0; sorry_warnings=0; fresh_olean=yes

FINAL SUMMARY: Catalog and facade PASS; errors=0; sorry_warnings=0.
Both target axiom footprints: [propext, Classical.choice, Quot.sound]; no sorryAx.
```

Required axiom-print results:

```text
'Turing.FinTM.exists_loopTM_spaceUsed' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.FinTM.computesFunInTime_pairMapSnd_spaceUsed' depends on axioms: [propext, Classical.choice, Quot.sound]
```

### Environment note

The pinned toolchain and dependency cache were reused from the prior agent's local environment; this checkout's `.lake/packages` points to that pinned dependency tree. `lake exe cache get` was run here, and TCSlib modules were checked into this checkout's own `.lake/tcslib-check-oleans` tree.

This execution environment cannot resolve the stock binaries' `/proc/<current numeric pid>/exe` lookup. The same external `LD_PRELOAD` shim as the prior delivery maps only that exact self-process path to `/proc/self/exe`. Its source is included as `environment/self_exe.c`. It does not change Lean proof terms, the kernel, toolchain sources, or repository files. No `native_decide`, axiom declaration, unsafe proof mechanism, FFI proof hook, or admission was introduced. On a normal environment this shim is unnecessary; if needed, compile it outside the repository with `cc -shared -fPIC -o self_exe.so self_exe.c -ldl` and set `LD_PRELOAD` to that absolute shared-library path before running the pinned stock binaries.

Other chapter-3/4 statement surfaces retain their out-of-scope admissions. The zero-sorry claim here concerns the completed §12 layer and this owned file, not the whole repository.

## Requested shared lemmas

None required for this delivery. All new helpers remain private in the owned file. No shared-file edit was made.

## Escalations

None. Neither frozen statement was weakened or repaired.

## New private source declarations

Every new source declaration is listed below in file order. Compiler-generated constructors, recursors, the derived `DecidableEq` instance, and equation/instance internals belong to their private source declarations. All 45 declarations are complete; none contains an admission.

| # | Kind | Name |
|---:|---|---|
| 1 | inductive | `a2_MapState` |
| 2 | instance | `a2_mapStateFintype` |
| 3 | def | `a2_mapAct` |
| 4 | def | `a2_mapTM` |
| 5 | def | `a2_mapCfg` |
| 6 | def | `a2_mapVirtual` |
| 7 | lemma | `a2_mapCfg_read` |
| 8 | lemma | `a2_map_move` |
| 9 | lemma | `a2_map_first` |
| 10 | lemma | `a2_map_block` |
| 11 | lemma | `a2_map_suffix` |
| 12 | lemma | `a2_map_backB` |
| 13 | lemma | `a2_map_backA` |
| 14 | lemma | `a2_map_emit` |
| 15 | lemma | `a2_map_finish` |
| 16 | lemma | `a2_map_parse` |
| 17 | lemma | `a2_map_setup` |
| 18 | lemma | `a2_mapVirtual_step` |
| 19 | lemma | `a2_mapVirtual_run` |
| 20 | def | `a2_mapEntered` |
| 21 | lemma | `a2_mapSetup_stationary` |
| 22 | lemma | `a2_mapSetup_step` |
| 23 | lemma | `a2_mapSetup_run` |
| 24 | lemma | `a2_mapSetup_head_step` |
| 25 | lemma | `a2_mapSetup_heads` |
| 26 | lemma | `a2_map_launch` |
| 27 | lemma | `a2_map_reject` |
| 28 | def | `a2_mapSumEquiv` |
| 29 | lemma | `a2_map_sum` |
| 30 | lemma | `a2_map_space` |
| 31 | lemma | `a2_source_radius` |
| 32 | def | `a2_heads` |
| 33 | lemma | `a2_heads_mono` |
| 34 | lemma | `a2_heads_steps` |
| 35 | lemma | `a2_heads_join` |
| 36 | lemma | `a2_heads_halted` |
| 37 | lemma | `a2_call_heads` |
| 38 | lemma | `a2_fuel_heads` |
| 39 | lemma | `a2_call_run` |
| 40 | lemma | `a2_call_prefix` |
| 41 | lemma | `a2_loop_prepare` |
| 42 | lemma | `a2_loop_start_prefix` |
| 43 | lemma | `a2_loop_round` |
| 44 | lemma | `a2_segments` |
| 45 | lemma | `a2_loop_halted_run` |

## Archive and integration

The archive contains this report, the full owned source, two ordered format patches, `fill-s12-f2-A2.bundle`, `final-sweep.log`, `axioms.log`, `SHA256SUMS`, reproducible audit/axiom inputs, and supplemental environment/bootstrap evidence. Report and verification files are delivery artifacts outside the repository; the commit series touches only the owned Lean file.

From the archive directory, run `sha256sum -c SHA256SUMS`. To integrate, start from the recorded base and apply the two files listed in `patches/series` with `git am -3` in order. Alternatively, fetch branch `fill/s12-f2-A2` from the bundle into a repository that already contains the recorded base. The included patch-replay log confirms the reconstructed tree equals the delivery tree.

After the pinned dependencies and bootstrap modules are available, rerun the two `lean_check_tree.sh` commands shown above, then run `verification/axioms.lean` with the scratch olean tree first in `LEAN_PATH`. `verification/audit_owned_file.py <repository-root>` rechecks the frozen material against the recorded base; `verification/check_style.py <repository-root>` invokes the repository's campaign checker on the owned file.

## Local notation

`n` is the complete input length; `a,b` are decoded pair components. In the loop proof, `ℓ` is fuel-bit length, `B` is the common head radius, `k` is host tape count, and `c₀` is the received time coefficient. In the map proof, `D=5*(n+1)` bounds administrative head positions and `u` is the first payload-entry time. R4's `A,B` denote space/time coefficients only in its constants paragraph; they are `22,5`. Integer intervals include both endpoints. All Lean identifiers retain their source meanings.
