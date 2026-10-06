# Chapter 2, epoch 4, batch A2 — verified partial checkpoint

**Incomplete. No additional public target is closed.** This delivery banks
**52 new proved private declarations** for the native preparation phase:
an exact arithmetic-header producer, faithful silent virtual-reference
simulation, a bounded reference runner, and a binary counter with a proved
administrative frame. The four original assigned admissions remain untouched.
There are no new admissions. The five-target completion gate does not pass.

The complete packed-record producer is still open, so this checkpoint is
**earlier than the brief's suggested complete-producer boundary**. In
particular, it does not provide a serialized trajectory, last-visit search,
complete startup, emission body, or equisatisfiability proof. This is the
verified partial delivery permitted by the continuation provision, with the
remaining frontier stated below.

## Provenance and ownership

- Repository: `https://github.com/Shilun-Allan-Li/tcslib`.
- Source branch checked out: `complexity/arora-barak-ch1`.
- Observed source tip carrying the binding continuation brief:
  `290bccf804c922ca5a9453619e4ab4b989ae28e0`.
- Required, resolved, and actual base:
  `f815da304646e3347d8fdb23723d8b51d254e4cc`.
- Working branch: `fill/ch2-e4-A2`, created directly at the required base.
- Delivery commit: **4dfebedfa1042ba990ff936548a6c5307d86d5b6**.
- Delivery tree: **60d39864020422bce159be3023fe1227c4238eb0**.
- Sole changed repository path: `TCSlib/Complexity/CookLevin/Hardness.lean`.
- The source branch and remote-tracking branch remain at the observed tip.
  No other branch modification, push, or PR. Single-agent execution.

The continuation brief was read first, followed by the committed predecessor
REPORT and original brief. The contribution policy/workflow, phase-4
resolutions and findings (including the boundary table and Derivations B/C),
emitter stage mapping and closing resolutions, snapshot contract, and
relevant native construction records were read. The external prior-art
proof was not retrieved or used.

## Public targets, in their required order

| Target | Status |
|---|---|
| `NPHard.polyTimeReducible` | Already proved at the base; unchanged; empty admission roots. |
| `SAT_NPHard` | Original admission unchanged. The new native components support the first continuation step, but that step is not complete. |
| `SAT_NPComplete` | Original admission unchanged; deferred until hardness is closed. |
| `SAT3_NPHard` | Original admission unchanged. Its reduction dependency `SAT_reducible_SAT3` is now proved and is separately checked clean. |
| `SAT3_NPComplete` | Original admission unchanged; deferred in order. |

There are **zero sanctioned admitted dependencies**. The four owned roots
are unfinished assigned work, not completed proofs with an allowance. The
only out-of-scope source admission is `TAUTOLOGY_coNPComplete`.

## Banked native components

| Component | Result |
|---|---|
| Exact NP witness extraction | `clNPVerifier` extracts the original coefficient and degree, retains the exact certificate equivalence, and calls the inherited `clObliviousVerifier`. Only verifier time is enlarged. |
| Native arithmetic assembly | `clNative_linear/map/pair/append/unary` assemble proved public catalog machines with their sequential runtime bounds. Pairing preserves the original input needed by both computed fields. |
| Actual all-false-input scan | `clFillTM`, `clFill_run`, `clNative_fill` implement a zero-work-tape native scan. Each input bit contributes the chosen constant bit; the boundary transition halts silently. Empty input is included. |
| Exact retained header | `clPrepHeader`, `clPrepHeader_native`, `clPrepHeader_machine` produce the retained instance, exact binary certificate length, exact binary reference length, exact binary horizon, the all-false virtual input, and the unary horizon clock. The entire output is charged to its native runtime. |
| Silent source step and full frame | `clRefCfg`, `clRefAction`, `clRef_apply` implement virtual clamping over a stored buffer, disjoint source tapes, arbitrary administrative-bank actions, preserved native input, and unchanged physical output. The source's optional state is stored inside a live host state. |
| Faithful running schedule | `clRefTM`, `clRef_run`, `clRef_initial`, `clRef_schedule` identify all running head positions with the exact public all-false reference schedule at every source time. Initial state, blank source tapes, zero work heads, and virtual input head one are explicit. |
| Actual horizon control | `clRefClockTM`, its configuration and step/run/return/first/initial lemmas, and `clRefClock_bound` provide a native unary-clock controller. Its source-time invariant includes both zero and the horizon. After the last source step, one silent administrative transition enters a distinct live return state. |
| Native binary increment | The `clCount*` family implements carry and rewind in place. It returns the canonical successor word, restores the counter head to zero, preserves the native input head, and emits nothing. The completion time is cut to an actual strictly positive first return. |
| Counter work preserves the reference | `clRef_admin` gives the one-action frame. `clRefCountTM`, `clRefCount_frame`, and `clRefCount_first` lift the actual native counter routine into an administrative bank and preserve the whole virtual input/source configuration throughout the call. |

The header's exact fields are

```text
pairEncode x
  (pairEncode (Nat.bits Q)
    (pairEncode (Nat.bits m)
      (pairEncode (Nat.bits T)
        (pairEncode (List.replicate m false) (List.replicate T true)))))
```

Here `Q = C*(|x|+1)^e`, `m = |x|+Q`, and
`T = c*(A*(m+1)^d+1)^2`. No arithmetic coefficient or degree positivity is
needed by the header producer, so the zero cases are handled exactly.

**The header is not the complete packed-record output.** It was not
substituted for that output at the install bridge. In fact this continuation
does not make a new install-call instantiation. The complete producer must
first extend the header with the actual trajectory and last-visit records.

## Six-row contract and boundary-check mapping

| Stage | New discharge and exact remaining boundary |
|---|---|
| s1 — exact arithmetic | `clNPVerifier` preserves the certificate parameters. `clPrepHeader_native/machine` supply an actual producer retaining the instance and all exact arithmetic answers, plus the literal reference input and clock. Public composition/capture contracts include complete answers, including any final-transition output. **Open:** integrate header parsing and arithmetic into the one complete record producer and its silent preparation return. The header transducer alone outputs its header; it is not advertised as the final silent startup. |
| s2 — reference simulation | `clRef_initial` and `clRefClock_initial` establish the complete prepared source initialization; `clRef_apply/run/schedule` prove literal agreement with the all-false reference run, including virtual clamping, arbitrary physical input, and disjoint source banks. **Open:** produce this prepared multi-tape layout from the real input inside the complete controller; include retained records and administrative banks in that actual startup. |
| s3 — output and halting | `clRefAction/apply` suppress source output and retain halt internally, while copying its work writes and moves before changing internal state. No condition on the successor state excludes terminal writes or erasures. `clRefClock_run/first` continue the frozen source through the whole horizon and return only on clock exhaustion. **Open:** consume these proved components in the full record-producing controller. There is no assembled complete producer whose output-isolation invariant can yet be claimed. |
| s4 — inclusive trajectory | `clRefClock_run` supplies every running configuration at times `0..T`; `clRefClock_return` does not advance the source. `clCount_seam`, `clCount_width`, `clRef_admin`, and `clRefCount_first` prove native binary increment and whole-source preservation during actual administrative work. **Open:** connect the appropriate counter changes to actual signed/clamped source displacements, define the stored position-record format, and copy every row, including the initial and final rows, into a packed word. An inclusive running invariant is not a stored trajectory. |
| s5 — greatest earlier visits | The predecessor's pure `clPrev_spec` remains unchanged. **No new native search is supplied.** Still open: search all strictly earlier stored records, compare signed positions, retain the greatest matching time or `none`, handle the empty time-zero search and immediately preceding frozen visits, and prove a sequential-access runtime ledger. |
| s6 — serialization | The predecessor's fixed templates, chunk identity, exact unary ledger, and conditional emitter theorem are unchanged. **No new emitter body is supplied.** Ordered rounds, cursor updates, clean positive returns (including empty/saturated rounds), fuel, the common budget, and its application remain open. |

The two initial-seam lemmas concern a **prepared** `Cfg.ofWords`; neither
claims the missing genuine `initCfg` startup. The counter seam is complete
for its own one-tape module, and its framed variant retains the source bank;
neither is the missing whole-producer clean seam.

The protected family order, `R` versus `R+1`, and sole-last-terminator chunk
rule are unchanged. The future native common budget `P` must cover startup,
fuel, and every whole round. It is not the tableau horizon `T`.

## Runtime facts actually proved

| Native component | Proved cost |
|---|---|
| Complete arithmetic-header computation and answer length | One fixed polynomial `a*(|x|+1)^r`, via the native polynomial-time composition calculus. |
| Bare bounded reference runner from its prepared seam | Exactly `T+1` transitions: `T` source steps and one silent dispatch; `clRefClock_bound` gives its polynomial majorant in the original instance length. |
| In-place binary increment | Exactly `2*clCountCarry(w)+2` transitions to its absorbing return; the actual first return is positive and at most `2*|w|+2`. |
| Framed increment | The same first-return bound, `2*|Nat.bits v|+2`; the source bank is unchanged. |
| Binary counter width | `v < 2^w` implies `|Nat.bits v| ≤ w`. |

These are component ledgers. No overall recording/search ledger, common
emitter budget, or reduction runtime is claimed. The inherited quadratic
formula-output bound was not reused as a native-runtime bound.

## Exact continuation frontier

Continue the binding four-step plan, beginning inside step 1:

1. **Finish the complete packed-record producer.** Use the proved exact
   header, unpack it into the actual retained-instance/clock/buffer layout,
   and use `clRefAction` with its whole-configuration proof as the source
   transition. Assemble signed-position counters and inclusive row recording;
   `clRefCount_first` is an actual framed binary-increment component, not an
   already assembled position tracker. Preserve effects-first terminal
   transitions, suppress the reference verdict, and keep halted positions
   frozen. Implement greatest-strictly-earlier sequential searches and charge
   every comparison, scan, dispatch, and record-copy operation. The full
   producer, including this total ledger, is still the natural checkpoint.
2. **Install the complete packed result, then establish genuine startup.**
   The install bridge must receive the completed producer. Retain the
   instance, add the bounded emission cursor, and prove the entire canonical
   `Cfg.ofWords` seam from native `initCfg`, including all administrative
   buffers and heads.
3. **Build the ordered emission controller.** Use the protected finite
   tables and exact `clChunk` order. Prove every positive first return,
   full scratch restoration, cursor update, positive silent saturated round,
   fuel evaluation, and one common polynomial `P` for all startup/fuel/round
   work.
4. **Establish output identity before semantics.** Instantiate
   `clEmitter_of_body` and `clTableau_chunks`. Then prove pure
   equisatisfiability by pinning recovery and strong induction with the
   snapshot APIs and bitwise product slices, using the exact singleton
   decider output at the horizon for acceptance. Close `SAT_NPHard`, then
   its three corollaries in order. All four closed targets must have empty
   admission roots; `SAT_reducible_SAT3` is proved.

No mathematical obstruction was found. **Escalations: none. Requested
shared lemmas: none.** No unproved new helper or construction assumption has
been added to the delivered source.

## Freeze and construction provenance

`verify-freeze.py` deletes exactly the new contiguous private block and
recovers the entire base source **byte for byte**. Thus all five public
statements and proofs, all 77 predecessor private declarations, all existing
docstrings, imports, options, and declaration order are unchanged. No old
docstring was edited. Every new declaration is private.

The arithmetic pairing proof locally repeats the public-catalog assembly
used in `ClassNP/TMSAT.lean`, with no cross-file private reference. The
counter carry/rewind family is locally harvested from
`ClassP/TimeConstructible.lean` at the base. Its deliberate machine change
is explicit: carry/rewind use a silent, absorbing live return instead of the
original length counter's input-scanning state; native input is never
advanced and no counter emission phase exists. The carry/rewind contracts
are rechecked on this new machine, and new first-return, canonical-seam,
and reference-frame proofs discharge the changed interface.

Final source: **2112 lines, 104989 bytes**; **919 insertions, zero deletions**.
SHA-256: `9a7fc5d442e1d56c1ab44f1370bb339b047bcf39b35fa14dd9a14ff4c97c71b1`.
The existing size exception continues: exclusive ownership requires all new
helpers to remain private in `Hardness.lean`; splitting a shared module
would violate this brief. Style lint reports **0 FAIL, 1 size WARN**.

## Verification

| Gate | Final result |
|---|---|
| Fresh ordered sweep | **57/57**, exit 0; zero `error:` diagnostics; 57 fresh nonempty oleans. |
| Admission diagnostics | Exactly **5**: the four untouched owned targets and the untouched out-of-scope `TAUTOLOGY_coNPComplete`. |
| Kernel closure traversal | **PASS** over all **375** owned checked kernel declarations, including generated declarations. All 129 private source declarations (77 inherited + 52 new) are admission-free, with at most `propext`, `Classical.choice`, `Quot.sound`. |
| Public targets | Target 1 clean; the four unfinished targets each retain exactly their own root. `SAT_reducible_SAT3` is printed and checked with empty roots. |
| Dependency regressions | The emitter loop, both clean-call bridges, exact polynomial-bit evaluator, oblivious normalization, snapshot locality, and SAT/SAT3 membership are checked clean. |
| Public surface | **PASS**: exactly the five original public declarations; every addition, including generated kernel declarations, is private. |
| Freeze and ownership | **PASS**: original source reconstructed byte for byte; only `Hardness.lean` differs; clean working tree at the delivery commit. |
| Style | 0 FAIL, one documented file-size WARN. |
| Transport | Format-patch replay reproduces the exact committed tree; incremental bundle verification passes. |

The closure walker inspects checked kernel types and opaque values, traverses
inductive constructors, and fails on missing declarations. Its expected
roots explicitly describe a partial checkpoint. This is **not** a pass of
the five-target completion gate.

The initial bootstrap compiled all 49 prerequisites and then exposed ordinary
errors in the in-progress owned block. After correction, the owned module and
all later modules passed (`bootstrap-completion.log`). The final full sweep
used an independent, initially empty output tree. Earlier failed iterations
are not presented as successful sweeps. A later execution-session reset
interrupted a sweep at module 34; it was discarded and the final sweep
restarted from an empty output tree.

Final sweep tail:

```text
TCSlib/Complexity/CookLevin/Hardness.lean:2103:8: warning: declaration uses 'sorry'
TCSlib/Complexity/CookLevin/Hardness.lean:2109:8: warning: declaration uses 'sorry'
CHECK 51/57 TCSlib/Complexity/ClassNP/Tautology
TCSlib/Complexity/ClassNP/Tautology.lean:1271:8: warning: declaration uses 'sorry'
CHECK 52/57 TCSlib/Complexity/TuringMachine
CHECK 53/57 TCSlib/Complexity/ClassP
CHECK 54/57 TCSlib/Complexity/Uncomputability
CHECK 55/57 TCSlib/Complexity/Formulas
CHECK 56/57 TCSlib/Complexity/CookLevin
CHECK 57/57 TCSlib/Complexity/ClassNP
FULL_SWEEP_COMPLETE 57/57 2026-10-06T04:10:42.467933+00:00
```

Final traversal result:

```text
CHECKPOINT_AUDIT_PASS: 129 source private declarations; 375 owned kernel declarations including generated declarations; all inherited and new helpers admission-free; all five public targets unchanged, with exactly the four original later targets open; SAT_reducible_SAT3 clean. This is not the five-target completion gate.
```


## New private declaration inventory

All names are private in `Complexity`:

```text
clNPVerifier
clNative_linear
clNative_map
clNative_pair
clNative_append
clNative_unary
clFillTM
clFill_run
clNative_fill
clPrepHeader
clPrepHeader_native
clPrepHeader_machine
clRefCfg
clRefAction
clRef_apply
clRefTM
clRef_run
clRef_initial
clRef_schedule
clRefClockTM
clRefClockCfg
clRefClock_step
clRefClock_run
clRefClock_return
clRefClock_first
clRefClock_initial
clCountInc
clCountCarry
clCountInc_bits
clCountInc_length
clCountBump
clCountTM
clCountTape
clCountCfg
clCountTape_read
clCountTape_write
clCount_carry_step
clCount_carry
clCount_rewind
clCountCarry_le
clCount_run
clCount_idle
clCount_idle_run
clCount_first
clCountTape_eq
clCount_seam
clRef_admin
clRefCountTM
clRefCount_frame
clRefCount_first
clCount_width
clRefClock_bound
```

## Delivery and reproduction

The flat `fill-ch2-e4-A2.zip` includes this REPORT, complete `Hardness.lean`,
a format-patch, incremental git bundle, final fresh sweep and axiom logs,
freeze and public-surface checks, private inventory, environment/dependency
pins, and `SHA256SUMS` at the root. `Hardness.lean` maps to the sole owned
repository path above. The git bundle requires the recorded base.

Verify extracted contents with `sha256sum -c SHA256SUMS`. Integrate the
format-patch on the maintainer's chosen branch containing the base. The
included `RUN_CHECKS.sh` accepts the repository path and a new absolute
verification directory and runs the ordered sweep, kernel closure check,
public-surface check, and exact freeze check in the pinned environment.

The stock Lean runtime used the inherited process-path compatibility shim:
`proc_exe.c` maps only the current process's numeric executable-path lookup
to `/proc/self/exe`. Compiler and kernel bytes are unchanged. Ordinary
runtimes need no shim. `lake exe cache get` was run exactly once and
succeeded (7,506 files unpacked); all 11 dependency checkouts match their
manifest pins with no tracked changes. No `lake build` ran.

**Notation:** `x` is the original instance; `C,e` are its unchanged
certificate coefficient and degree; `Q=C*(|x|+1)^e`; `m=|x|+Q`; `M` is the
fixed oblivious verifier; `c,A,d` are normalized verifier-time constants;
`T=c*(A*(m+1)^d+1)^2`; `R` is the inherited final emission-round index
(member count `R+1`); `P` is the distinct, still-unconstructed common
native-loop budget. `a,r` are existential runtime-polynomial constants;
`v` is an unsigned binary-counter value; `w` denotes a counter word in the
carry ledger and a bit-width in the width lemma. `|·|` denotes word length.
`clCountCarry` counts initial true bits cleared by an increment. Existing
Lean identifiers keep their source meanings.
