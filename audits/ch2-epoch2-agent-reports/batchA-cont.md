# Chapter 2 E2 continuation, batch A — completed enumerator

`enumMachine_contracts` is proved without an in-scope admission, through the required `Turing.FinTM.exists_loopCfgTM` route. Its frozen statement is unchanged. The existing outer proofs of `NP_subset_EXP`, `HALT_NPHard`, and `HALT_not_mem_NP` are unchanged and now have no admitted dependency.

The four required axiom prints contain exactly `[propext, Classical.choice, Quot.sound]`; checked-kernel dependency traversal finds an empty admission-root set for each. All 95 new named private helpers and their 252 declarations including generated descendants are also admission-free. The only source-level admission remaining in the owned file is the unchanged, out-of-scope `EXP_subset_NEXP`.

## Provenance and scope

- Repository: `https://github.com/Shilun-Allan-Li/tcslib`.
- Required campaign branch: `complexity/arora-barak-ch1`.
- Exact base: `64d82f84dfbbfcd7b5d69689dc0f37fb3d3116c4`.
- Work branch: `fill/ch2-e2cont-A`.
- Delivered commit: `336f016e28deff86fdcd01dcb5859e150cc0b0a6`.
- Delivered tree: `19890a9d28b1f93c0baeada742a0e97946bcbe48`.
- Parent of the delivered commit: the exact required base above.
- Lean: 4.25.0, release commit `cdd38ac5115bdeec5f609e9126cce00f51ae88b3`.
- Mathlib: `029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e`.
- Single Codex agent; no delegation, push, or PR.

The continuation brief was read from the named campaign branch before implementation. The checkout for the delivered source is pinned to its required base, not a newer branch tip. The infra round-3 item 5, machine-library-design sections 9b/9c, original E2-A brief and predecessor report, policy, workflow, and repository agent instructions were read as binding context. `main` was not used as the work base.

Only `TCSlib/Complexity/ClassNP/EXP.lean` changes in Git. The precise import `TCSlib.Complexity.TuringMachine.Build.Primitives` is added. All new implementation declarations are private and distinctly named. Report, instruments, and logs are delivery artifacts outside the Git patch.

## Construction and six-contract mapping

A source block shares work tapes between the unary initializer, the prepared verifier composition, and the prepared increment composition. Each call is wrapped by a finite logging and restoration machine. Logging saves the old symbol and head displacement for each source work tape at each live source step, with a separate unary clock. The public capture simulation suppresses physical emissions and writes the source output to a dedicated capture tape. Reverse replay restores each original work cell and head, erases every history cell, then rewinds the native input and capture heads. Thus the reset is a proved complete-configuration equality, including the buffer, rather than an assumption that clearing is free.

| Required contract | Discharging construction and lemmas |
|---|---|
| Width evaluation and initialization | `computesFunInTime_polyUnary C c` supplies the explicit unary width. `enumCont_lift_init`, `enumCont_body_call`, `enumCont_body_start`, and `enumCont_body_start_guarded` run it, copy each true mark as a false candidate bit, erase the marks, and restore the native head to 1 and every work head to 0. The resulting candidate has exactly the prescribed width; native input is read-only and retained. |
| Fixed-width increment and overflow | `computesFunInTime_incFixed` is invoked on the candidate alone by `enumCont_increment_call`. `enumCont_increment_cases`, `enumCont_body_check`, `enumCont_copy_complete`, and `enumCont_body_increment` copy a successful equal-width result onto candidate tape 0 in place, erase capture, and rewind. Empty overflow output retains the old word. `enumCont_inc_eq`, `enumCont_step_length`, and `enumCont_orbit` bridge this stalled step to the predecessor's proved rank enumeration. The exported fuel controls exhaustion, including the one empty-word round at width zero. |
| Buffering, retention, and verifier-call simulation | `enumCont_concat_native`, `enumCont_concat_candidate`, and `enumCont_concat_run` emit exactly `x ++ s`. `enumCont_prepared_comp`, `enumCont_round_seam`, and `enumCont_verifier_call` use the proved buffered composition, correct virtual input boundaries, and fresh verifier tapes. `enumCont_lift_call` places this prepared call in the shared source block. The clean wrapper restores the retained candidate and source work. |
| Capture and return | `enumCont_clean_capture` instantiates the public `Turing.capture_run` with the clean controller as host for the logged source. That source contains the actual supplied verifier in the buffered composition. `enumCont_clean_complete`, `enumCont_return_run`, and `enumCont_body_call` capture the completed output, including a halting-transition emission, restore work, and redirect the first halt to live administration. `enumCont_body_accept` emits exactly `[true]`; `enumCont_body_reject` erases the false verdict before increment. No source emission reaches the physical output. |
| Restart | `enumCont_log_apply`/`enumCont_log_run` prove the trace, and `enumCont_restore_cell`, `enumCont_undo_back`, `enumCont_undo_write`, `enumCont_undo_run`, and `enumCont_clean_restore` undo it exactly. `enumCont_rewind`, `enumCont_clean_buffer_rewind`, and `enumCont_clean_complete` restore native/capture positions. `enumCont_clean_entry_words`, `enumCont_clean_exit_words`, `enumCont_copy_complete`, and `enumCont_pair_words` identify the complete blank-scratch seam. All restoration costs are included in the body budget. |
| Timed loop invariant | `enumCont_body_round_raw` composes verdict dispatch, clean increment, copy, and rewind. `enumCont_first_anchor` and `enumCont_halt_transfer` transfer runs from a controller variant with an absorbing anchor; `enumCont_body_start_guarded` and `enumCont_body_round_guarded` prove the exact startup and positive, strict-interior-anchor-free round contracts. `enumCont_common_bound` supplies one uniform polynomial. `enumCont_from_body` applies the audited loop export and translates its conclusion to the frozen interface. The predecessor's unchanged `enumDecider`, `enumLoop_run`, and `enumBudget_bound` finish the public result. |

The stopped-controller device is proof machinery only: it differs from the active body solely at the anchor. A rejecting run uses its first anchor visit, whose complete configuration equals the bounded endpoint because that anchor is absorbing. An accepting stopped run could not have visited the live absorbing anchor. Adding the actual body's one-step departure proves strictly positive round time and excludes all strict interior returns.

## Exact loop instantiation

Write `n = x.length`, `w = C * (n + 1)^c`, and `N = n + w + 1`. Let `fU` be the initializer's catalog coefficient and `j` the incrementer's coefficient. `enumCont_common_bound` chooses, before `x`,

- body coefficient `A = 3*a + 3*fU + 3*j + 60`;
- body degree `D = d + c + 2`.

The body startup is bounded by `3*TU + n + 3*w + 10`, with `TU = fU*(n+1)^(c+1)`. A round is bounded by `3*TV + 3*TI + 2*n + 3*w + 22`, where `TV ≤ a*N^d + 2*(n+w) + 4` and `TI ≤ (j+3)*(w+1)`. Both are at most `A*N^D`.

| `exists_loopCfgTM` argument or hypothesis | Exact instance / evidence |
|---|---|
| `body`, `anchor` | `enumCont_bodyTM B qv qi false`, administrative state `.inr 0`. `B = enumCont_sources Q R U`, where `Q` is buffered concatenation followed by `MV`, `R` is candidate-only concatenation followed by the catalog incrementer, and `U` is the catalog unary width generator. |
| `Inv x s` | `s.length = C * (x.length + 1)^c`. |
| `s0 x` | `List.replicate (C * (x.length + 1)^c) false`. |
| `stepF x s` | `(incFixed s).getD s`, preserving width on overflow. |
| `acceptF x s` | `MultiTapeTM.indicator V (x ++ s)`, computed by the captured prepared call to the hypothesis machine `MV`. |
| `R n` | `2^(C*(n+1)^c) - 1`. |
| `hF` | A direct second `computesFunInTime_polyUnary C c` catalog instance with coefficient `fF`; `enumCont_fuel_bits` proves `Nat.bits (2^w-1) = List.replicate w true` by induction, using `Nat.bit1_bits` at successor width. No alternate fuel evaluator is used. |
| common `T n` | `(A + fF) * (n + C*(n+1)^c + 1)^(D+c+1)`, dominating both body and fuel costs. |
| `hInv0` | `List.length_replicate`. |
| `hInvStep` | `enumCont_step_length`, derived through `enumCont_inc_eq` and the proved in-file `enumInc_spec`. |
| `hstart` | `enumCont_body_start_guarded` plus the first component of `enumCont_common_bound`, then domination by `T`. |
| `hround` | `enumCont_body_round_guarded` plus the second component of `enumCont_common_bound`, then domination by `T`. Includes positive time, the strict-interior anchor exclusion, singleton acceptance, and the exact restored next seam. |

The conclusion translation is exactly infra round-3 item 5:

1. `enumCont_orbit` proves the orbit equals `enumWord w i` for `i < 2^w`, using the in-file `enumWord_zero` and `enumInc_word`. It makes no false claim about the terminal orbit value at `2^w`.
2. `1 ≤ 2^w` gives `(2^w - 1) + 1 = 2^w`. The exported terminal state and `[false]` output are rewritten to this exact frozen index.
3. The configuration family is used unchanged, and each exported in-range round is rewritten by the bounded orbit identity.
4. If the export coefficient is `K`, take `b = K*(A+fF+1)` and `e = D+c+1`. Since `1 ≤ N^e`, the frozen budget dominates `K*(T n + 1)`. Coefficients and degrees are fixed before the input. At width zero the fuel is zero but the loop still tests the unique empty candidate before rejecting.

## Statement freeze and size

`freeze.py` verifies all 46 existing declarations remain in their original order, with the same six public declarations and no removals. Only the proof body of `enumMachine_contracts` differs. Its signature is identical. All 46 pre-existing docstrings remain verbatim and in order.

A stronger byte check deletes the newly inserted helper region and completion note, restores only the target's old `sorry` proof, and removes the permitted import. The result is byte-for-byte identical to the base file. This covers every old private family, every unchanged public proof, original header/options, and the out-of-scope admission. In particular no `enumCarry*`, `enumCapture*`, or `enumLoop_run` declaration was edited.

An append-only completion note after the filled target explains that the historical partial-fill descriptions are superseded. Those frozen descriptions themselves were not edited.

The final file is **2887 lines** (base: 882), with six public and 135 private declarations. Its source SHA-256 is `ce21b2543c7acf883d29921e042aeda808c92d564b4483eba3ca9e00ae08e9c6`. This extends the recorded 600-line-target overrun and exceeds the 1000-line split threshold. The positive justification is the binding single-file ownership: all newly required machine/controller proofs must remain private in `EXP.lean`, while the superseded old families must be retained unchanged until E5 deduplication. Splitting or moving these implementations would violate this fill's ownership/freeze constraints. The size is explicitly reported for subsequent closure/refactoring review.

Requested shared lemmas: **none**. Statement escalations: **none**. No frozen statement repair was needed.

## Verification

The required `lake exe cache get` was invoked once, narrowed to the campaign's Mathlib roots, and succeeded. No `lake build` was run. The working olean tree was bootstrapped in dependency order, with the owned module checked during proof iteration and all 14 later modules successfully checked after the final owned-file edit. Failed development iterations were not treated as gate passes.

The final sweep uses the committed 57-module order and a new output tree, `.lake/e2cont-A-final-oleans`, which did not exist at launch. Each module is checked through the committed `lean_check_tree.sh`: zero exit status, no error diagnostics, and a freshly produced olean are required. The completed gate results and exact log tail follow.

The full fresh sweep passed **57/57 modules**, produced 57 fresh oleans, and reported **zero errors**. The 27 admitted-declaration warnings are all out of scope. Final sweep tail:

```text
TCSlib/Complexity/ClassNP/Tautology.lean:130:8: warning: declaration uses 'sorry'
MODULE 52/57 TCSlib/Complexity/TuringMachine
MODULE 53/57 TCSlib/Complexity/ClassP
MODULE 54/57 TCSlib/Complexity/Uncomputability
MODULE 55/57 TCSlib/Complexity/Formulas
MODULE 56/57 TCSlib/Complexity/CookLevin
MODULE 57/57 TCSlib/Complexity/ClassNP
SWEEP_PASS modules=57
```

The axiom/root instrument runs against that same fresh tree. It uses the committed closure-audit template's traversal of checked kernel constant types and values, including opaque bodies and inductive constructors. It resolves the private target by its user name, prints all four targets, rejects every axiom outside the standard triple, and requires empty roots. It also checks every new helper and generated descendant, including helpers outside the target's dependency closure.

Final axiom and root output:

```text
'_private.TCSlib.Complexity.ClassNP.EXP.0.Complexity.enumMachine_contracts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
ROOTS Complexity.enumMachine_contracts: []
'Complexity.NP_subset_EXP' depends on axioms: [propext, Classical.choice, Quot.sound]
ROOTS Complexity.NP_subset_EXP: []
'Complexity.HALT_NPHard' depends on axioms: [propext, Classical.choice, Quot.sound]
ROOTS Complexity.HALT_NPHard: []
'Complexity.HALT_not_mem_NP' depends on axioms: [propext, Classical.choice, Quot.sound]
ROOTS Complexity.HALT_not_mem_NP: []
NEW_IMPLEMENTATION_PASS named_helpers=95 declarations_with_descendants=252 roots=[]
ENUMERATOR AUDIT PASS: all four required closures have empty admission roots and at most the standard axiom triple.
```

`git diff --check` passes. The ClassNP policy lint has zero FAIL and two size WARNs: this reported 2887-line `EXP.lean` and the unchanged 1206-line `TMSAT.lean`. The owned-file Lean check emits only the expected out-of-scope admission warning, with no new simplifier/tactic warnings.

The pinned installed toolchain was reused. This executor requires the supplied `proc_self_compat.c` readlink compatibility shim: it redirects only the current process's `/proc/<pid>/exe` lookup to `/proc/self/exe` so Lean finds its standard library. It does not alter Lean, source, kernel behavior, or proof checking. Normal environments do not need the shim. `environment.log` records the actual toolchain version and dependency pin.

## New private declarations

All 95 source-level additions are listed below in declaration order. Names are in namespace `Complexity`; implementation-generated descendants are covered by the kernel check. No new public declaration is introduced.

| Name | Role |
|---|---|
| `enumCont_inc_eq` | The catalog counter and the predecessor's counter have the same recursive equations, including overflow on the empty word. |
| `enumCont_step_length` | Stalling on overflow preserves the exact candidate width. |
| `enumCont_orbit` | Before exhaustion, the stalled catalog orbit is exactly the predecessor's rank enumeration. |
| `enumCont_fuel_bits` | The exact fuel word is a unary all-true word of the certificate width. |
| `enumCont_sparse` | A history tape can contain blank entries; its length is tracked on a separate all-true clock tape. |
| `enumCont_sparse_append` | Appending a possibly blank history symbol writes just the next cell. |
| `enumCont_sparse_erase` | Erasing the last history cell recovers its prefix, even if the erased entry was itself blank. |
| `enumCont_moveCode` | Three tape symbols encode the three source head moves. |
| `enumCont_unmove` | Decode the inverse move for the backward restoration pass. |
| `enumCont_unmove_cast` | A recorded move and its inverse cancel as integer head displacements. |
| `EnumContEntry` | A history entry retains every overwritten symbol and every source move. |
| `enumCont_logAction` | Instrument one source action with a clock cell and two history tracks per source tape. |
| `enumCont_logTM` | The logged source keeps its original finite state set. |
| `enumCont_logCfg` | The correspondence stores exactly the source configuration and the finite history; every history head is one cell past the recorded entries. |
| `enumCont_log_apply` | One logged action preserves source semantics and appends exactly one history entry, including a halting or emitting action. |
| `enumCont_history` | Record precisely the actions actually executed by a source run. |
| `enumCont_log_run` | Logging is lockstep with the source, from arbitrary prepared source configurations. |
| `enumCont_undoTM` | The restoration controller alternates inverse head movement with writing the old symbols. |
| `enumCont_undoCfg` | At a restoration checkpoint the heads inspect the last remaining history entry. |
| `enumCont_undoResult` | The completed restoration retains exactly the source's initial work fields and leaves every history tape blank with its head at zero. |
| `enumCont_restore_cell` | Undoing a tape write at the old head restores its original contents, including no-write actions and writes of blank. |
| `enumCont_clock_erase` | Erasing the last clock mark exposes exactly the preceding clock word. |
| `enumCont_undoMid` | Between inverse movement and inverse writing, the source heads are back at their old positions and the last history entry is already erased. |
| `enumCont_undo_back` | The first restoration transition reverses the last source head moves, retains the old symbols in finite control, and erases their history cells. |
| `enumCont_undo_write` | The second restoration transition writes the retained old symbols and backs the history heads up to the preceding entry. |
| `enumCont_undo_empty` | With no history left, one silent transition restores the history heads to zero and halts. |
| `enumCont_undo_run` | A logged live source prefix can be completely undone in `2t+1` steps. |
| `enumCont_first_halt` | Any known halted endpoint is reached at the first halting time, with a live source at every earlier time. |
| `enumCont_bufferAction` | Administrative actions preserve the source bank and only move the native input and the final capture tape. |
| `enumCont_undoEntry` | Entry into restoration moves all history heads from the right blank to the newest entry, leaving source heads fixed. |
| `enumCont_cleanTM` | A clean subroutine logs and captures a source, undoes all source work, rewinds the native input and captured word, and halts silently. |
| `enumCont_cleanCfg` | Clean administrative configurations expose only the native and capture heads. |
| `enumCont_clean_capture` | The clean subroutine's first phase is the public captured simulation of the logged source. |
| `enumCont_clean_undo_entry` | After source halt, one silent dispatch parks every history head on its last entry and starts the captured restoration, retaining the source output. |
| `enumCont_clean_restore` | The captured restoration returns within `2t+1` steps with the original source work restored and its completed output retained separately. |
| `enumCont_buffer_apply` | Moving the clean subroutine's two exposed heads preserves every tape and the empty physical output. |
| `enumCont_rewind` | A mandatory left step followed by a boundary scan restores the native head in at most its old position plus two steps. |
| `enumCont_clean_buffer_rewind` | The retained output word rewinds without being erased. |
| `enumCont_clean_complete` | A halting source call can be made clean: retain its output on the final tape, restore every source work field, blank all histories, and rewind both exposed heads. |
| `enumCont_concatTM` | The assembly source emits native input followed by the candidate already on its sole work tape. |
| `enumCont_concatCfg` | Assembly configurations keep the candidate word fixed while exposing the input head, candidate head, and emitted prefix. |
| `enumCont_concat_native` | The native-input scan emits exactly the remaining input and switches to the candidate phase, preserving the candidate and its head at zero. |
| `enumCont_concat_candidate` | The candidate scan appends the exact tape word to the emitted native input and halts at its right blank. |
| `enumCont_concat_run` | Assembly from the candidate seam emits exactly `x ++ s` in `\|x\|+\|s\|+2` steps. |
| `enumCont_prepared_comp` | Buffered composition also works from a prepared first-machine work configuration. |
| `enumCont_round_seam` | The prepared assembly source occupies tape zero; the composition buffer and verifier work tapes are exactly blank at the candidate seam. |
| `enumCont_verifier_call` | The prepared verifier call accepts the exact assembled input `x ++ s`. |
| `enumCont_returnAction` | Relabel live states and redirect halt to a live return state, preserving the complete action. |
| `enumCont_returnCfg` | The live-return correspondence preserves all configuration fields except the control state, including work-tape results. |
| `enumCont_return_run` | A host with the redirected transition table simulates a source through its first halt and returns the exact completed configuration. |
| `enumCont_clean_verifier` | Combining the prepared verifier call with the clean wrapper gives a repeatable call: the candidate is retained, all other original source work is restored to blank, and the sole verdict is held on the capture tape. |
| `enumCont_padAction` | Pad an action with inactive high tapes and embed its finite control. |
| `enumCont_padCfg` | Pad a source configuration with blank stationary high tapes. |
| `enumCont_pad_apply` | Padding commutes with one action; the new high tapes remain blank. |
| `enumCont_pad_run` | A machine may run on an initial tape block of a larger controller. |
| `enumCont_sources` | Three finite source routines share a common padded tape block. |
| `enumCont_endsAction` | Move or write the candidate at tape zero and the final capture tape, preserving every intervening tape. |
| `enumCont_bodyTM` | The concrete body uses one clean source block for initialization, verification, and increment. |
| `enumCont_increment_call` | Starting assembly in its candidate phase supplies just that candidate to the catalog incrementer. |
| `enumCont_pad_words` | Padding preserves the candidate-on-zero convention when the source has at least one work tape. |
| `enumCont_pad_init` | The same padding identity for empty initial work is valid even when the source machine has no work tapes. |
| `enumCont_overwrite` | Overwriting the first remaining candidate cell extends the completed prefix and drops the old cell, also when the old word is initially empty. |
| `enumCont_sparse_clear` | The erased capture prefix consists entirely of blanks. |
| `enumCont_pairCfg` | Tape configurations for the administrative copy and rewind scans. |
| `enumCont_ends_apply` | The two-ended administrative action changes exactly those tape cells and their common head, preserving native input and physical silence. |
| `enumCont_sparse_blanks` | A sparse list of blank entries is an everywhere blank tape. |
| `enumCont_sparse_some` | Lifting every word symbol into the sparse representation gives the usual buffer tape. |
| `enumCont_copy_scan` | The copy scan overwrites the candidate from left to right and erases each captured symbol. |
| `enumCont_pair_rewind` | Rewind the two endpoint heads together across the completed candidate. |
| `enumCont_copy_complete` | Copying a captured word at least as long as the old candidate completely replaces it, erases capture, and restores the canonical seam in linear time. |
| `enumCont_log_words` | Empty history adds only blank stationary tapes to a candidate seam. |
| `enumCont_extend_words` | Appending one output tape to a candidate seam has the two-endpoint tape layout used by the administrative controller. |
| `enumCont_clean_entry_words` | The clean wrapper's entry configuration at a prepared source seam. |
| `enumCont_clean_exit_words` | The completed clean call has restored the candidate seam and retained only its captured output on the last tape. |
| `enumCont_body_call` | A clean call inside the body redirects the clean wrapper's first halt to the appropriate live administrative state. |
| `enumCont_pair_words` | With empty capture and zero endpoint heads, the administrative tape layout is exactly the public canonical candidate seam. |
| `enumCont_body_start` | Initialization runs the clean unary generator, copies its marks as false candidate bits, erases the marks, and rewinds to the canonical anchor. |
| `enumCont_body_depart` | A genuine round leaves the anchor in one silent stationary transition. |
| `enumCont_body_accept` | A captured true verdict emits the sole physical accepting bit and halts. |
| `enumCont_body_reject` | A false verdict is erased before entering the clean increment call. |
| `enumCont_increment_cases` | The catalog's empty overflow output preserves the old candidate. |
| `enumCont_body_check` | The increment-result check preserves all fields and chooses the anchor on overflow or the copy phase on a nonempty result. |
| `enumCont_body_increment` | A clean increment call followed by copy and rewind implements the exact stalled fixed-width step. |
| `enumCont_body_round_raw` | Starting just after departure, one verifier call either emits acceptance or clears the verdict and completes one exact candidate update. |
| `enumCont_absorb` | An anchor whose transition is a stationary self-loop preserves its complete configuration for every subsequent step. |
| `enumCont_agree_run` | Two transition tables differing only at the anchor agree on every run prefix that has not yet visited that anchor. |
| `enumCont_first_anchor` | The first visit to a stopped anchor transfers to the active machine with the same full endpoint and no earlier anchor visit. |
| `enumCont_halt_transfer` | A halted stopped run never visited the live absorbing anchor. |
| `enumCont_body_agree` | The active and stopped body have identical transitions away from the anchor. |
| `enumCont_body_start_guarded` | Startup satisfies the loop export's first-anchor guard as well as its full canonical configuration equality. |
| `enumCont_body_round_guarded` | The active round has positive duration and no strict interior visit to the anchor. |
| `enumCont_lift_call` | A prepared source call may use the initial tape block of the shared source machine; padding preserves its halt and exact emitted word. |
| `enumCont_lift_init` | Initial calls pad correctly even for a zero-work-tape source. |
| `enumCont_common_bound` | One input-independent polynomial bounds both body phases. |
| `enumCont_from_body` | A concrete body with polynomial startup and exact seam restoration gives the frozen enumerator configuration contract by the audited loop export. |

## Flat delivery and reproduction

The archive is `fill-ch2-e2cont-A.zip`, with every member at the archive root and `SHA256SUMS` at the root. `EXP.lean` is the complete modified source for repository path `TCSlib/Complexity/ClassNP/EXP.lean`. The numbered patch series and incremental bundle contain the single recorded commit, with the exact required base as the bundle prerequisite. `git bundle verify` succeeds. `replay_patch.py` applies the patches in a temporary index without checking out or changing any branch, and reproduces the delivered Git tree exactly.

After extracting the flat archive, verify `sha256sum -c SHA256SUMS`. With the pinned toolchain and dependencies available, the included instruments can be run from the extracted directory:

```bash
python3 freeze.py --repo /path/to/tcslib
python3 sweep.py --repo /path/to/tcslib --oleans /path/to/new-fresh-olean-tree
python3 run_axioms.py --repo /path/to/tcslib --oleans /path/to/new-fresh-olean-tree
python3 replay_patch.py --repo /path/to/tcslib
```

The sweep output path should be new and empty. The axiom check must use the sweep's output path. Intended maintainer integration is `git am -3` of the supplied patch; this delivery performs no integration, push, or PR.

The ZIP also includes the freeze, policy lint, owned/downstream checks, final sweep, final axiom/root, environment, cache-setup, bundle-verification, and patch-replay logs, plus the verification instruments and optional executor compatibility source.

## Glossary

- **Seam:** the complete configuration expected between subroutines: native input head 1, work heads 0, candidate on tape 0, blank scratch, and empty physical output.
- **Anchor:** the live controller state marking a candidate seam.
- **Stalled increment:** a fixed-width increment that keeps the old word when overflow occurs; fuel, not the stalled state, determines exhaustion.
- **Admission root:** a checked kernel declaration whose type or body directly mentions `sorryAx`, found by traversing the full dependency closure.
- **`fU` / `fF`:** fixed catalog coefficients for the initializer and the separately obtained loop-fuel generator, respectively.
