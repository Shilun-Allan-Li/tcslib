# Chapter 2, epoch 4, batch A — verified partial checkpoint

**Incomplete: 1 of 5 public targets closed.** `NPHard.polyTimeReducible`
is proved. The Cook–Levin target and its three corollaries retain their
original admissions. This delivery banks **77 proved private declarations**,
including a concrete pure tableau formula, its product encoding and fixed
templates, exact ordered serialization and size bounds, an exact native
certificate-length call, and conditional emitter-loop assembly. There are
**no new private admissions**. The five-target completion gate does not pass.

This is the continuation checkpoint expressly permitted by the brief's
“continuation certain” provision. No claim is made that the record producer,
native tableau-emitting body, or tableau equisatisfiability has been proved.

## Provenance and scope

- Repository: `https://github.com/Shilun-Allan-Li/tcslib`.
- Source branch checked out: `complexity/arora-barak-ch1`; `main` was never used.
- Observed source tip: `61cf595831e920854f4f047796478a8913ad90a1`.
- Governing brief: `briefs/ch2-epoch4-batchA.md` at that tip, as expressly
  authorized by the user's follow-up correcting the filename.
- Required, resolved, and actual base:
  `f57cf9c1f0835a2336b93a61c6a6e4c9b1b266f0`.
- Local working branch: `fill/ch2-e4-A`. Only this new, initially clean
  branch was moved from the observed tip to the required base.
- Delivery commit: `dbe35d8c4ec56626ede8e0aee86cd8d31f40d068`.
- Delivery tree: `f34f43fb0a0c04b54f5f235204fd0088a2a49367`.
- Sole modified repository file: `TCSlib/Complexity/CookLevin/Hardness.lean`.
- The source and remote-tracking branch refs remain at the observed tip.
  No push, PR, or modification to any other branch; single-agent execution.

The brief, policy/workflow, campaign plan, phase-4 resolutions and both
findings records (including Derivations B/C), emitter stage mapping,
round-3 findings, emitter fill resolutions, emitter W/L/P/P2 reports,
snapshot batch-C report, inherited environment/pitfall briefs, and the
committed closure-audit template were read. The external prior-art file
was neither retrieved nor used.

## Targets in the required order

| Order | Target | Exact status |
|---|---|---|
| 1 | `NPHard.polyTimeReducible` | Closed by the proved reduction transitivity calculus. Empty admission roots. |
| 2 | `SAT_NPHard` | Original `sorry` untouched. The private checkpoint below is proved, but is not yet connected to this public target. |
| 3 | `SAT_NPComplete` | Original `sorry` untouched; deferred until target 2 closes. |
| 4 | `SAT3_NPHard` | Original `sorry` untouched. `SAT_reducible_SAT3` remains the one sanctioned eventual dependency; it is printed and audited separately. |
| 5 | `SAT3_NPComplete` | Original `sorry` untouched; deferred in order. |

Targets 2–5 each currently have their own admission root. Those roots are
**open assigned work**, not sanctioned completed proofs. In particular,
targets 1–3 are not collectively admission-free, and targets 4–5 do not
yet meet their eventual one-sanctioned-root condition.

## What the checkpoint proves

| Component | Declarations and result |
|---|---|
| Exact family order/count | `clGroups`, `clLastRound`, `clGroups_length`; sizes are `n, 1, T, T+1, k(T+1), T`. Work members are ordered by time, then tape. `clTableauGroups_length` specializes the count to the actual formula. |
| Exact word identity | `clFragment`, `clChunk`, `clChunks_before`, `clChunks_serialize`, `clGroups_serialize`, `clTableau_chunks`. Only the last chunk gets `[false]`. An empty group still occupies its round; an empty last group still contributes the sole formula terminator. No whole-formula serializer is called per group. |
| Unary ledger | `clSerializeLit_length`, `clSerializeClause_length`, `clSerialize_length`: exactly one final bit, two bits per clause, and `v+3` per literal occurrence. `clPins_length` gives the separate pinning contribution `n(n-1)/2 + 5n`. |
| Variable packing | `clPack_disjoint`, `clPack_injective`, `clPack_lt`: input/snapshot disjointness, quotient/remainder uniqueness, and the inclusive-time ceiling. |
| Positive-time verifier normalization | `clObliviousVerifier`: enlarge the verifier's time coefficient and degree only, apply the proved time-constructible oblivious conversion, and exclude zero simulation multiplier with `not_computesInTime_zero`. |
| Explicit horizon bounds | `clHorizon_lower`, `clInputLength_bound`, `clHorizon_upper`. Certificate length remains exactly `C(n+1)^e`; its upper bounds never replace it. |
| Actual native certificate arithmetic module | `clCertificateCall`: instantiate `computesFunInTime_polyBits` and `exists_installCallTM`. At first positive exit the complete binary answer is installed, scratch is blank, heads are canonical, and physical output is empty, over arbitrary native input. The call has bound `a(arg.length+1)^(e+1)` for a fixed coefficient. No positivity hypothesis on `C` or `e`. |
| Product encoding and junk handling | `CLFieldCode`, `clFieldCode`, symbol encoders, `clBlockEncode`, the three slice functions, `clBlock_state/input/work`, `clBlock_ext`, `clBlock_injective`, `clBlockDecode`, `clBlockDecode_encode`. State/input/work fields are consecutive bit slices. Every junk whole block decodes to the same halted/blank snapshot. Bitwise field equality determines the raw block; decoded equality is not substituted. |
| Fixed finite templates | `clTemplate`, `clTemplate_spec`, `clTemplate_eval`, `clTemplate_wiring`, `CLTemplateKind`, `clPredicate`. Templates are selected once from Claim 2.13 for the fixed machine and code. All reconstruction windows have constant arity `2B+1`. Relabeling allows repeated indices. |
| Concrete pure tableau | `clWire`, `clGroup`, `clInputGroup`, `clWorkGroup`, `clTableauGroups`, `clTableau`. Initial, state, input, work and acceptance predicates are explicit. Pinning members are unit clauses. Boundary inputs use a blank table and a safe dummy index; previous visits use the public strict-earlier schedule definition. |
| Actual formula size | The `CLBounds` and group/flatten bound lemmas culminate in `clTableau_length` and `clTableau_quadratic`. These bound the concrete pure formula, not an unspecified future family. |
| Conditional native assembly | `clCursor_orbit`, `clLoop_polyBound`, `clEmitter_of_body`. Given the complete startup, positive first-return round, exact chunk, packed-word update and fuel contracts, the proved emitter library computes precisely the serialized pure group concatenation in polynomial time. All construction hypotheses remain explicit. |

The raw block width is positive even with zero work tapes. The finite state
code uses a safe cardinality-sized bit width; no one-hot consistency-clause
family is added. Templates pin the actual encoded field bits. The helper
`clPrev_spec` obtains both strict-earlier membership and maximality directly
from the filtered-range maximum; no foreign private locality lemma is cited.

The output-size corollary assumes the exact verifier-input length is at most
the horizon, as supplied by normalization. Its explicit coefficient is

`1 + (k+4) * 2^(2B+1) * (2 + (B+3)*(2B+1))`,

and its bound is that coefficient times `(T+1)^2`. This is an **output-size**
bound. It does not charge reference recording, sequential access, cleanup,
or native round computation, and is not asserted to bound their runtime.

## Six-row contract and boundary-check mapping

| Stage | Discharged part and exact remaining boundary |
|---|---|
| s1 — exact arithmetic | `clCertificateCall` installs exact `Q` on a prepared argument and includes zero coefficient/degree, halting-transition answer bits, positive observed return, and empty physical output through the proved clean-call interface. `clObliviousVerifier` and the horizon lemmas settle normalization/estimates. **Open:** native retained-instance setup, exact computation of `m` and `T`, and assembly into complete packed preparation records. The clean certificate call alone is not the startup producer. |
| s2 — reference simulation | The pure formula uses exactly the inherited `inputPosAt`/`prevVisit` reference schedule at `m = n+Q(n)`. **Open:** native virtual `false^m` simulation with source initial state, blank work tapes, zero work heads, input head 1, clamping to `0..m+1`, and disjoint banks. No claim that native input `x` can substitute for this reference. |
| s3 — output and halting | No reference-simulation controller is supplied. **Open:** prove effects-first terminal writes/moves, suppress reference emissions, retain halt internally, and continue frozen configurations through the horizon. Early rejection and a final-step halt remain explicit obligations. The conditional `clEmitter_of_body` requires silent canonical startup; it does not discharge it. |
| s4 — inclusive trajectory | `clTableauGroups`, `clTableauGroups_length`, `clPack_lt` and group bounds include all times `0..T` and state-successor targets through `T`. **Open:** native recording before step 1 and after step `T`, exact signed/clamped counters, and proof that administrative scans do not advance the simulated clock or corrupt represented configuration. |
| s5 — greatest earlier visits | `clWorkGroup` uses exactly `prevVisit`; `clPrev_spec` proves its strict-earlier/greatest semantics and `clWorkGroup_bounds` uses the strict bound. **Open:** the native record-search algorithm, empty candidate handling at time zero, preservation of frozen post-halt positions, and an explicit sequential-scan/comparison runtime ledger. The pure specification is not a native search implementation. |
| s6 — serialization | Concrete fixed templates, correct family order, `R+1` chunks, the sole last terminator, exact unary length ledger and quadratic output-size bound are proved. `clEmitter_of_body` gives conditional polynomial native assembly and requires positive rounds even when chunks are empty. **Open:** construct the actual body and packed state/cursor representation, prove first-return and full clean seams, account for every scan/dispatch/unary emission, and instantiate the conditional lemma. |

The install bridge for the actual startup must receive a producer of the
**complete packed records**, not a machine returning only a verifier verdict.
There is no such producer in this checkpoint. `clCertificateCall` is a
component call with a deliberately narrower, explicitly stated result.

The last-round value is `R = n + (k+3)T + k + 1`; the executed member count
is `R+1`. The abstract cursor saturates at `R+1`. Its invariant is closed
beyond the executed prefix, its emission specification at saturation is
empty, and its native round hypothesis still requires positive duration.
The common budget in `clEmitter_of_body` is named `P`: it must bound fuel,
startup and every entire round. It is distinct from the tableau horizon.

## Exact continuation frontier

There is no concrete `pack`, `stepF`, `emitF`, `body`, `anchor`, fuel machine,
or common budget satisfying `clEmitter_of_body` for `clTableau`. There is also
no proof of `clTableau` equisatisfiability. Do not close the target through
any of the still-admitted public theorems.

1. Extract the original NP witness, keep its exact certificate coefficient
   and degree, instantiate `clObliviousVerifier`, and choose `clFieldCode`
   for the optional state field. Construct the **complete** exact-arithmetic
   and reference-record producer with all s1–s5 invariants above, including
   inclusive trajectory and greatest-earlier searches. Give its full
   sequential-tape polynomial bound.
2. Install that packed result silently, retain the instance, and add the
   bounded cursor. Prove genuine startup from `initCfg` to the canonical
   `Cfg.ofWords` seam; include every administrative buffer and head.
3. Build the ordered round controller using the already fixed `clPredicate`
   tables and `clWire` arithmetic. Produce the exact `clChunk`, update the
   cursor, restore the complete seam, and prove strict positive first return.
   Include a positive silent saturated round. Supply the exact fuel evaluator
   and one common polynomial bound for startup, fuel and rounds.
4. Apply `clEmitter_of_body` and `clTableau_chunks` to establish the actual
   machine's output equals `serialize (clTableau ...)`. **Then** prove pure
   equisatisfiability: recover the exact-length certificate from pinning;
   strong induction over time with the proved snapshot APIs and bitwise
   product slices; no-false-emission acceptance using the total decider's
   exact singleton output at the horizon. No semantic theorem is to be
   defined in terms of the emitting machine.
5. Close `SAT_NPHard` via that reduction and `decode_serialize`, then close
   targets 3–5 in order. Require targets 1–3 empty-rooted and allow only
   `SAT_reducible_SAT3` for targets 4–5. Re-run the fresh sweep and closure
   checker with the new expected roots.

No mathematical obstruction or statement escalation was found. **Requested
shared lemmas: none.** No shared or sibling file was changed.

## Freeze, size and declarations

`verify-freeze.py` removes the single new private block and restores only
target 1's original `sorry`, recovering the entire base source **byte for
byte**. This checks every original signature, docstring, import, option,
declaration order and the four other proof bodies. No original docstring
was altered or deleted; new helpers have their own documentation/sketches.

Final source: **1,193 lines, 58,578 bytes**; diff **957 insertions, 1 deletion**.
SHA-256: `cefb15199d60b6fb658855d35f33afed787f744fbfadbee5ab151d5a2f4e6738`.
Style lint: **0 FAIL, 1 size WARN**. The positive justification for keeping
the coherent checkpoint together above 1,000 lines is the brief's exclusive
ownership of `Hardness.lean` and requirement that all helper declarations
remain private there. A split into another source file would violate this
batch's ownership. No public declaration was added. The kernel-level public-surface check
caught automatically generated instances from an unused `deriving` clause;
that clause was removed, and the final sweep and root/surface checks were
re-run on the corrected source.

The complete 77-name source inventory is appended below and is also in
`private-inventory.json`. All names are private in `Complexity`.

```text
clLastRound
clGroups
clGroups_length
clFragment
clFragment_append
clChunk
clChunks_before
clChunks_serialize
clGroups_index
clGroups_serialize
clSerializeLit_length
clSerializeClause_length
clSerialize_length
clClause_cost_le
clSerialize_length_le
clPack
clPack_disjoint
clPack_injective
clPack_lt
clObliviousVerifier
clHorizon_lower
clCertificateCall
clInputLength_bound
clHorizon_upper
clLoop_polyBound
clPins
clPins_length
clLiteralCount_le
clSerialize_uniform
clTemplate
clTemplate_spec
clTemplate_eval
clLiteral_lt_numVars
clTemplate_wiring
CLFieldCode
clFieldCode
clSymbolCode
clSymbolDecode
clSymbolDecode_code
clBlockEncode
clStateSlice
clInputSlice
clWorkSlice
clBlock_state
clBlock_input
clBlock_work
clBlock_ext
clBlock_injective
clBlockDecode
clBlockDecode_encode
clWidth
clSourceBits
clTargetBits
clWindowBit
CLTemplateKind
clPredicate
clWire
clGroup
clInputGroup
clWorkGroup
clTableauGroups
clTableau
clTableauGroups_length
clTableau_chunks
CLBounds
clGroup_bounds
clCeiling_pos
clInputGroup_bounds
clPrev_spec
clWorkGroup_bounds
clPin_bounds
clTableauGroups_bounds
clFlatten_bounds
clTableau_length
clTableau_quadratic
clCursor_orbit
clEmitter_of_body
```

## Verification and delivery

| Gate | Final result |
|---|---|
| Fresh ordered sweep | **57/57**, exit 0; zero `error:` lines; 57 nonempty fresh oleans. |
| Existing admission diagnostics | 11: the four untouched owned targets and seven out-of-scope declarations. No new admission. |
| Kernel closure traversal | **PASS** over all 221 owned kernel declarations, including generated declarations. Target 1 and all 77 new private source declarations have empty admission roots and at most `propext`, `Classical.choice`, `Quot.sound`. The four original later targets have exactly their own open roots. |
| Sanctioned dependency | `Complexity.SAT_reducible_SAT3` explicitly printed and checked with exactly its own root; none of the banked helpers uses it. |
| Dependency regressions | Emitter loop, both clean-call bridges, exact polynomial bits, oblivious normalization, snapshot work locality, and SAT/SAT3 membership all have empty admission roots. |
| Public surface | **PASS**: exactly the five original public declarations. All additions, including generated kernel declarations, are private. |
| Statement freeze and ownership | **PASS**: original source reconstructed byte for byte; only `Hardness.lean` differs; working tree clean at the recorded commit. |
| Style | 0 FAIL, 1 documented size WARN. |
| Delivery transport | Format-patch replays to the exact committed tree; incremental bundle verifies. |

The closure traversal inspects checked kernel declaration types and opaque
values, follows constructors of inductive declarations, and treats missing
declarations as failures. Its checkpoint expectations explicitly distinguish
the four open assigned targets from completed proofs. It is **not** a pass
of the eventual five-target completion gate.

Final sweep tail:

```text
TCSlib/Complexity/ClassNP/Tautology.lean:1271:8: warning: declaration uses 'sorry'
CHECK 52/57 TCSlib/Complexity/TuringMachine
CHECK 53/57 TCSlib/Complexity/ClassP
CHECK 54/57 TCSlib/Complexity/Uncomputability
CHECK 55/57 TCSlib/Complexity/Formulas
CHECK 56/57 TCSlib/Complexity/CookLevin
CHECK 57/57 TCSlib/Complexity/ClassNP
FULL_SWEEP_COMPLETE 57/57 2026-10-06T02:26:31.580447+00:00
```

Final closure-check result:

```text
CHECKPOINT_AUDIT_PASS: 77 source private declarations; 221 owned kernel declarations including generated declarations; target 1 and every new helper admission-free; exactly the four original later targets open. This is not the five-target completion gate.
```


Pinned environment: official Lean 4.25.0 at
`cdd38ac5115bdeec5f609e9126cce00f51ae88b3`, mathlib
`029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e`; all 11 materialized dependency
checkouts match their manifest revisions with no tracked modifications.
`lake exe cache get` ran once and succeeded, decompressing 7,506 files.
No `lake build` ran. The original executable-location failure was resolved
by the included `proc_exe.c` readlink shim, which maps only the current
process's numeric executable path to `/proc/self/exe`. Compiler and kernel
bytes were not modified. Normal environments need no shim.

The bootstrap first compiled the 49 prerequisites, then exposed ordinary
errors in the in-progress owned block. The corrected owned module passes its direct check, and the final full
sweep also verifies every later module. The final sweep starts with an
empty output tree. Earlier failed attempts are not presented
as successful full sweeps.

The flat `fill-ch2-e4-A.zip` includes this report, full `Hardness.lean`, the
single format-patch, incremental git bundle, final sweep and axiom logs,
closure checker, freeze checker/results, inventory, environment/cache
evidence, style output, and root-level `SHA256SUMS`. The root source maps
to the sole repository path above. The bundle requires the recorded base.
Patch replay through a temporary index reproduces the exact delivery tree;
bundle verification passes. No other branch is used for replay.

Verify extracted contents with `sha256sum -c SHA256SUMS`. Integrate the
format-patch on the maintainer's chosen branch containing the base. For
rechecking, run the committed 57-module order with
`scripts/lean_check_tree.sh`, then run `ClosureAxioms.lean` with that fresh
olean tree first on `LEAN_PATH`, followed by the pinned dependency caches.
`python3 verify-freeze.py /path/to/repository` reproduces the source freeze.
The included `RUN_CHECKS.sh` accepts the repository path and a new absolute
verification-directory path and runs the same gates in a prepared pinned
environment; it refuses to reuse an existing output directory.

**Notation:** `n` is instance length; `C,e` are the unchanged certificate
coefficient/degree; `Q(n)=C(n+1)^e`; `m=n+Q(n)`; `M` is the fixed oblivious
verifier and `k=M.k`; `T` is its tableau horizon; `B` is its product-code
width; `R` is the last round index; `P` is the distinct common native-loop
budget; `v` is a literal's variable index. Helper-local `K,w,N` denote
clause-count, width and variable-index bounds, respectively.
