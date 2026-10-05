# Chapter 2 — E3 continuation A: verified partial checkpoint

**INCOMPLETE: 0 of 6 public targets closed.** This continuation adds 69 proved
private declarations for native split-search phases. The integrated search
body, its startup contract, and its complete round contract remain open.
All six original public admissions are unchanged. The six-target completion
gate **does not pass**. This is the partial continuation permitted by the
continuation brief and its B2 precedent, not a completed batch.

## Provenance and authorization

- Repository: `https://github.com/Shilun-Allan-Li/tcslib`.
- Required starting branch: `complexity/arora-barak-ch1`.
- Requested base in the continuation brief: `b75b67715ac2a8b09df5a7c61dd0ca898a1762d7`;
  that object was unavailable. The integration commit actually on the branch
  is **`b75b6771768244efbd7898b1d41becfe0f83385e`**, the source base used here.
- The base discrepancy was raised before proceeding. The user's authorization
  was: “If the brief and continuation files are there, you may proceed.
  Otherwise abort and let me know.” All required files were present.
- The remote branch tip inspected was `76b1aea001098e605d3391ff03346275f5652a35`.
  The continuation brief, `briefs/ch2-e3cont-batchA.md`, was read and retained
  from that tip before starting the work branch at the authorized integration
  base. The original brief and predecessor report were present at the base.
- Binding materials are included as `original-brief.md`, `predecessor-REPORT.md`,
  and `continuation-brief.md`. The predecessor's 35 private helpers are untouched.
- Working branch: `fill/ch2-e3cont-A`.
- Delivery commit: `9e9881691538d6ca18febd98ae5e3ee5429246d5`.
- Delivery tree: `ef4f96d91393d2d143ccc2174c874a7b00279aa7`.
- Single-agent execution. No push, PR, rebase, or modification of another named
  branch occurred. The temporary replay worktree was detached and removed.

## Target status, in required order

| Order | Target | Status |
|---|---|---|
| 1 | `ntime_expPow_subset_NEXP` | Partial phase construction only. The existing single native-body existential admission and the theorem proof are byte-identical to the base. |
| 2 | `NEXP_subset_iUnion_NTIME` | Untouched admission. Exponential reverse host not started. |
| 3 | `NEXP_eq_iUnion_NTIME` | Untouched admission; not filled ahead of its directions. |
| 4 | `EXP_eq_NEXP_of_P_eq_NP` | Untouched admission. The two exact padding checks and relocated captured decider remain future work. |
| 5 | `P_ne_NP_of_EXP_ne_NEXP` | Untouched admission; not filled ahead of target 4. |
| 6 | `EXP_subset_NEXP` | Untouched admission. The entire `EXP.lean` file is unchanged. |

There are five explicit target admissions in `Nondeterminism.lean` and one in
`EXP.lean`. Every new private has a proved body and empty kernel admission
roots. Each public target still depends only on its own original admission.
The complete sweep has 13 admission warnings: these six plus the unchanged
SAT reduction, TAUTOLOGY result, and Hardness five.

## Proved native components and exact limitations

| Obligation | Discharging declarations and boundary |
|---|---|
| Prepared virtual candidate and output isolation | `e3cEvalTM`, `e3cEvalCfg`, `e3c_eval_initial`, `e3c_eval_run`, `e3c_eval_first`. Guarded virtual simulation captures every emitted bit, including a halting emission; physical output stays empty and physical input head stays at one. The entry is exactly a prepared `stateWord` configuration. |
| Actual completed-state dispatch | `e3c_eval_first` chooses the first actual source halt and excludes earlier return-state visits. `e3c_first_entry`, `e3c_compare_first`, and `e3c_clear_first` establish actual positive first returns for absorbing phase endpoints. Mathematical deadlines are bounds only, not native clocks. These are phase-level contracts, not the body's anchor contract. |
| Track arbitrary source work and its cleanup extent | `e3cTrackTM`, `e3c_track_run`, `e3c_track_extent`, `e3c_track_support`. The native transformer uses `1+2*T` steps and three banks: source data, a contiguous visited interval, and an origin marker. It marks the newly reached cell before halting, preserving the final source emission. Every data cell is within the actual tracked interval, even if the data has blank holes. |
| Exact single-tape cleanup | `e3cClearTM`, `e3c_clear_run`, `e3c_track_clearable`, `e3c_clear_first`. One data/interval/origin triple returns blank with all three heads zero, within `6*T+7`, at an actual positive first return. This does **not** supply a controller over the complete source bank or clear administrative/capture buffers. |
| Full binary comparison | `e3cCompareTM`, `e3c_compare_run`, `e3c_compare_first` compare entire optional-bit words, including unequal lengths, then rewind both heads to zero. The bound is `2*(max |u| |v|+1)`. `e3c_bits_injective` and `e3c_binary_check` identify canonical equality with the exact split equation when the candidate is within the input. Comparison assumes its two input words and heads have already been prepared. |
| Pre-validation evaluation allowance | `e3c_candidate_envelope` proves `B*(|s|+1)^r ≤ (B*2^r)*(|w|+1)^r` for `|s|≤|w|+1`. `e3c_eval_budget` bounds both evaluation time and output length before any accepted-padding hypothesis. The `|w|+2` allowance is explicit; no logarithmic validity assumption is used. The complete round's common envelope remains unproved. |
| Right boundary, including empty candidate input | `e3cRightTM`, `e3c_right_endpoint`, `e3c_right_computes` run a native rightward scan after actual source halt, costing at most `|s|+2`, while retaining every source work tape and output bit. A mandatory positive move handles both blank boundary positions on empty input. |
| Composed evaluator phase with exact cleanup data | `e3c_prepared_eval_first` captures `e3cRightTM (e3cTrackTM M)`. It has a positive first return within `1+2*T+|s|+2`, retaining the exact source trace banks at deadline `T`, complete captured output, known virtual right boundary, physical input head one, and no physical output. Source absorption, not a clock, identifies the exact endpoint. |
| Exact accepting emission | `e3cSplitEmitTM` and `e3cSplitEmit_run` emit precisely `pairEncode (w.take |s|) (w.drop |s|)` in `|s|+|w|+3` steps. This uses the candidate only as a length counter and works for arbitrary candidate bits. The entry requires physical input head one, candidate head zero, blank scratch, and empty output; connecting that entry to evaluator cleanup remains open. This family is adapted in-file from the pinned `Build/Primitives.lean` emitter; no library source changed. |

## Exact remaining first-target frontier

No `body`, `anchor`, `A`, or `r` has yet been supplied to the existing existential.
The proved phase machines above are not a substitute for either required full
configuration contract:

1. From the genuine initial blank configuration on every input `w`, reach
   `Cfg.ofWords anchor (stateWord body.k [])` within
   `A*(|w|+1)^(r+1)`, with no earlier anchor visit.
2. From that same canonical seam with candidate `s`, for every `|s|≤|w|+1`,
   take a **positive** number of steps in the same input-length-only envelope,
   with no earlier positive anchor visit. On equality, halt with exactly the
   encoded native split. On failure, return the **entire configuration** to
   the canonical seam for `e3SplitStep w s`: blank scratch, zero work heads,
   native input head one, empty output, and the required candidate word.

The next continuation should implement and prove these remaining connections:

1. Define the actual finite controller and fixed tape layout. Implement genuine
   startup and the one-past-end candidate's positive silent stall. Neither is
   currently implemented as a body phase.
2. Embed `e3c_prepared_eval_first` on the candidate. Prepare the actual remaining
   suffix, run the binary length evaluator on it, and capture its output.
   Evaluation is charged before validity testing. Preserve the native input
   and candidate, and rewind the two comparison buffers from their actual
   capture heads before entering `e3cCompareTM`.
3. Relocate and sequence `e3cClearTM` over every tracked source triple. Prove
   full-bank equalities, clear both capture buffers and all suffix/controller
   scratch, and restore candidate and physical input heads. A per-tape cleanup
   theorem alone is insufficient, particularly across the host's finite-index
   embeddings. Success must meet the emitter's blank-scratch entry contract too.
4. On success enter `e3cSplitEmitTM` with empty physical output. On failure
   increment the candidate only where allowed and prove the exact canonical
   seam. Use the known candidate right boundary to prove its rewind, including
   the empty-word case; do not infer its side from a blank symbol alone.
5. Prove the body's global no-earlier-anchor conditions and common polynomial
   bound, including setup, evaluation, comparison, all cleanup, and restoration.
   Then apply the unchanged `e3_split_of_body` and `e3_verifier_of_split` to close
   target 1, and continue targets 2–6 in order.

The suffix-length machine, complete bank controller, and restore/increment
composition have not been hidden behind new admissions. They remain absent.
Requested shared lemmas: **none**. Statement escalations: **none**. The base
object discrepancy was handled by the explicit authorization above.

## Preservation, size, and all new declarations

Only `TCSlib/Complexity/ClassNP/Nondeterminism.lean` changes in git: 1,395
insertions and one deletion (the old docstring closing line is extended).
The new code is one inserted private block, followed by an append-only
continuation appendix in the first target's docstring. Removing just those
additions reconstructs the original file byte-for-byte. The complete suffix
beginning at `theorem ntime_expPow_subset_NEXP` is byte-identical to the base.
Every existing private, public statement, proof, import, and option is preserved.
`EXP.lean`, all out-of-scope admissions, and `TuringMachine/Build/` are untouched.

- `Nondeterminism.lean`: 4407 lines, 229682 UTF-8 bytes; SHA-256 `2198f269b70c70f329b095c63c06b4b4d5adb9656fceed807dfab14c6ee3ba79`.
- `EXP.lean`: 2534 lines, 132712 UTF-8 bytes; SHA-256 `312ab7a6c4b6c7b14db22acfd92ca2aeb2ab64c63bb3e6b33a074010a677d930`.

The brief records the owned-file size exception and requires the bespoke native
construction in-file. No library split or visibility change was made. The
ClassNP style lint reports **0 FAIL / 5 WARN**; all warnings concern existing
large modules (the owned two, SAT, TMSAT, and Tautology). Lean also reports
non-fatal tactic/simplification lint warnings; zero errors is not a claim of
warning-free source.

All 69 new source declarations are private and admission-free:

- `e3cIdleTM`
- `e3cEvalTM`
- `e3cEvalCfg`
- `e3c_eval_run`
- `e3c_eval_initial`
- `e3c_eval_first`
- `e3c_candidate_envelope`
- `e3c_take_succ_eq`
- `e3cCompareTM`
- `e3cCompareCfg`
- `e3c_compare_nonblank`
- `e3c_compare_scan`
- `e3c_compare_rewind`
- `e3c_compare_run`
- `e3cInterval`
- `e3cCleared`
- `e3c_cleared_step`
- `e3cClearTM`
- `e3cClearCfg`
- `e3c_clear_left`
- `e3c_cleared_zero`
- `e3c_cleared_all`
- `e3c_clear_scan`
- `e3c_origin_erase`
- `e3c_clear_origin`
- `e3c_clear_run`
- `e3cSpan`
- `e3c_span_extend`
- `e3cSlots`
- `e3cTrackTM`
- `e3cTrackCfg`
- `e3cTrackMid`
- `e3c_track_action`
- `e3c_track_stamp`
- `e3cLo`
- `e3cHi`
- `e3c_track_extent`
- `e3c_track_support`
- `e3c_span_zero`
- `e3c_track_initial`
- `e3c_track_run`
- `e3c_track_computes`
- `e3cSplitPos`
- `e3cSplitPos_read`
- `e3cSplitPos_succ`
- `e3cSplitEmitTM`
- `e3cSplitEmitCfg`
- `e3cSplitEmit_double`
- `e3cSplitEmit_separator`
- `e3cSplitEmit_suffix`
- `e3cSplitEmit_run`
- `e3c_span_interval`
- `e3c_track_clearable`
- `e3c_first_entry`
- `e3c_compare_first`
- `e3c_clear_first`
- `e3c_bits_injective`
- `e3c_binary_check`
- `e3c_eval_budget`
- `e3cRightTM`
- `e3cRightCfg`
- `e3c_right_step`
- `e3c_right_run`
- `e3cRightScan`
- `e3c_right_scan`
- `e3c_right_finish`
- `e3c_right_endpoint`
- `e3c_right_computes`
- `e3c_prepared_eval_first`

## Verification and environment

- **Fresh sweep: 57/57 modules**, 57 fresh nonempty oleans, exit 0,
  zero `error:` lines, and `FULL_SWEEP_COMPLETE`. The output directory was newly
  created and empty. This sweep includes every owned and downstream module.
- `ClosureAxioms.lean` traverses the checked kernel environment, both declaration
  types and values (including opaque values), and inductive constructors. It
  checks **69 source helpers / 212 new helper-and-generated declarations**,
  **83 predecessor helper-and-generated declarations**, and the public roots.
  Every helper closure has empty admission roots and axioms within
  `[propext, Classical.choice, Quot.sound]`.
- Five regression headlines remain closed: `ntime_poly_subset_NP`,
  `NP_subset_iUnion_NTIME`, `NP_eq_iUnion_NTIME`, `NP_subset_EXP`, and
  `mem_NP_iff_exists_length_le`.
- All six target axiom prints still include `sorryAx`, with exactly their own
  declarations as admission roots. `PARTIAL_CLOSURE_AUDIT_PASS` asserts these
  explicit partial expectations; it does **not** assert the completion gate.
- Surface preservation, `git diff --check`, bundle verification, and detached
  patch replay pass. Replay yields the identical complete tree `ef4f96d91393d2d143ccc2174c874a7b00279aa7` and
  byte-identical owned sources. `replay.log` retains an initial filename typo
  before the successful application; there was no patch conflict.
- Pinned Lean 4.25.0 (`cdd38ac5115bdeec5f609e9126cce00f51ae88b3`), mathlib
  `029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e`. All 15 manifest dependency
  revisions match and their tracked sources are unchanged.
- `lake exe cache get` was invoked **once** and failed while installing
  leantar because archive ownership changes were unsupported. This is not
  reported as a successful cache-get run. The extracted executable was moved
  to its expected versioned path; `RecoverCache.lean` then used the pinned
  cache API. It downloaded/unpacked 7,506 of 7,507 requested entries and retained
  a warning for one absent entry. All imports used by the fresh sweep worked.
- The toolchain archive similarly extracted files while reporting ownership
  errors. This host needed the included `proc_exe.c` adapter to resolve its own
  executable path; it changes only `/proc/<own pid>/exe` to `/proc/self/exe`.
  Lean and its kernel were not modified. Details and reproduction commands
  are in `environment.txt`.
- **No `lake build`** was run. All TCSlib compilation used the committed
  `scripts/lean_check_tree.sh`; the kernel audit used the same fresh olean tree.

Final sweep tail:

```text
CHECK TCSlib/Complexity/ClassNP/Tautology
TCSlib/Complexity/ClassNP/Tautology.lean:1275:8: warning: declaration uses 'sorry'
CHECK TCSlib/Complexity/TuringMachine
CHECK TCSlib/Complexity/ClassP
CHECK TCSlib/Complexity/Uncomputability
CHECK TCSlib/Complexity/Formulas
CHECK TCSlib/Complexity/CookLevin
CHECK TCSlib/Complexity/ClassNP
FULL_SWEEP_COMPLETE
```

## Archive and reproduction

The ZIP is flat. `SHA256SUMS` lists every payload except itself, with no nested
paths. The archive contains the report, full modified source, explicitly
unchanged `EXP.lean` reference snapshot, one format-patch, incremental git
bundle, exact proof audit and logs, preservation script/results, dependency
pins, recovery provenance, and the binding documents. `verification.json`
records machine-readable verification results.

Apply the format-patch with `git am` on the authorized integration base. The
bundle also requires that base commit and contains only the continuation branch
ref; it is not a full repository clone. Reproduce the module sweep from the
repository root with the pinned dependencies available:

```bash
export TCSLIB_OLEANS=/absolute/path/to/new-empty-olean-tree
while read -r m; do
  bash scripts/lean_check_tree.sh "$m" || exit 1
done < scripts/ab_ch1_module_order.txt
bash /absolute/path/to/unpacked-archive/run-axiom-audit.sh "$PWD"
python3 /absolute/path/to/unpacked-archive/verify_surface.py "$PWD"
```

Run `sha256sum -c SHA256SUMS` inside the extracted archive to check its payloads.
