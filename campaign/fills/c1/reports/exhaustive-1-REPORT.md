# C1 exhaustive replay — incomplete fill report

**INCOMPLETE: phase 0 (environment/bootstrap).**
`Turing.FinNDTM.exists_exhaustiveDecider` remains unproved, with its original
`sorry`. No proof phase is claimed complete. This is an environment-blocked
partial delivery under ground rule 9, not a completed fill or a passed verification gate.

The source changes are exactly the three authorized imports and the permitted
“Fill appendix (C1-E)” paragraph. Draft tactics were explored in scratch but were
not verified and are **not** included in the delivered source. No new declaration,
axiom, admission, machine implementation, or public statement was introduced.

## Pin and attachment verification

- Repository: `https://github.com/Shilun-Allan-Li/tcslib`.
- Initially checked-out branch: `complexity/arora-barak-ch3-4`.
- Initial campaign tip: `2cce48048b5875fae75d69ef70ee9032b6b5e744`.
- `git merge-base --is-ancestor 83ec6348b325f060cec2a917b45a4eda6e301d84 HEAD`: **exit 0**,
  before creating the fill branch.
- Fill branch: `fill/c1-exhaustive`, created at exactly `83ec6348b325f060cec2a917b45a4eda6e301d84`.
- Base: `83ec6348b325f060cec2a917b45a4eda6e301d84`.
- Delivery commit: `070b5b83d37e6adf291dfa0d1ee703c9f774e72c`; its sole parent is the base.
- No rebase, merge, cherry-pick, push, or PR was performed.
- Attached brief SHA-256: `4807189da7b90a0366d9f3bd1ddcb104a5e8b4d83119e621d4f1d09917b40535`
  (**matches**).
- Attached addendum SHA-256: `a25474c52b6b8e8bc1295fad48278b3356b8fed482d2e49c5874554f6d8d2928`
  (**matches**).
- The repository brief equals the attachment after replacing `@ANCESTOR@` with
  the base. The repository addendum matches its attachment byte-for-byte.
- Inputs were read from their supplied scratch paths, not through Library reads.

## Checklist

These ticks indicate that the requested reporting item is covered, **not** that
its proof or verification gate passed.

- [x] Target status/phase, base hash and ancestor result are stated above.
- [x] The first source edit was exactly the three imports in region (a).
  The only subsequent edit was region (d)'s appendix. Regions (b) and (c) were
  not edited. All other tracked files are unchanged.
- [x] New-declaration inventory: **none**. The window clear is pending; see below.
  The permitted appendix explicitly records the incomplete status.
- [x] Constant `C` and ledger: **not instantiated or proved**. Their outstanding
  construction obligations are listed below.
- [x] Promotion candidates and environment escalation are recorded below.
- [x] Rule 10: no new proof citations or definition unfoldings. The three imports
  are precisely the permitted ones. The original import probe was attempted
  and failed on missing upstream artifacts; there were no extra names to add.
  Rule 11's diff grep found neither the six canonical R3 rows nor any of the
  2,943 private names collected from the other 76 modules of the order list.
- [x] Both v3 screen outputs are quoted verbatim below. New pairs: **none**.
  **new copies: none**.
- [x] Final source size: **122 lines; 2 public / 0 private declarations**,
  versus 110 lines at the base. New declarations: 0. New lines over 100
  characters: 0. Sweep, probe, axiom, lint and freeze results follow.

## Environment escalation E1

Unmodified Lean 4.25.0 reported `error: failed to locate application`.
The addendum's exact source was used, with SHA-256
`985924ad83d39e108c0a2107bab07e65cdeb88641453508ab5acda115534fba7`.
It made both Lean and Lake version commands start successfully. The source is
included at `evidence/runtime/executable-path.c`; the compiled shared object is
not shipped. No permission change, sandbox escalation, toolchain modification,
or alternate readlink shim was used.

The exact runtime environment was:

```text
PATH=/workspace/scratch/8032237c75d4/runtime/lean-4.25.0-linux/bin:$PATH
LEAN_SYSROOT=/workspace/scratch/8032237c75d4/runtime/lean-4.25.0-linux
LAKE_HOME=/workspace/scratch/8032237c75d4/runtime/lean-4.25.0-linux
LD_PRELOAD=/workspace/scratch/c012fe960313/work/runtime/executable-path.so
LEAN_NUM_THREADS=1  (later diagnostic/final attempts)
```

`TCSLIB_OLEANS` pointed into this task's separate scratch output trees, ending
with `/workspace/scratch/c012fe960313/work/final-oleans`. The preload was scoped
to Lean/Lake/check/cache processes and was not exported globally. Runtime paths
are provenance for this host; they are not portable installation requirements.

Cache preparation first encountered disk exhaustion and an invalid compiled
Lake configuration. The requested cache command's automatic ProofWidgets
**no-build** validation attempted
`lake -v build --no-build proofwidgets:release` and failed; no build command was
invoked directly and no actual project build was run. This internal cache-tool
behavior is disclosed rather than hidden behind a claim that it never occurred.
The subsequent pinned hash lookup and leantar restoration recovered 115 missing
cached modules without changing any package source.

The shared host remained at essentially its 8 GiB cgroup memory ceiling.
A diagnostic reached the unchanged first module's Lean invocation and made no
observable elaboration progress for several minutes. Even after limiting this
task to one check and one Lean worker thread, no fresh first-module artifact
was obtained. Resource pressure is an inference supported by the recorded host
counters and stalls; it is not a proof that the source is erroneous.

**Requested continuation:** rerun the prescribed bootstrap on a host with enough
available memory and disk. Resume proof work only after that succeeds. No ground
rule was waived to substitute unchecked tactics for a checked proof.

## Verification results

| Check | Result |
|---|---|
| Attachment hashes, ancestor and exact base | PASS |
| Region ownership and byte comparison outside permitted regions | PASS |
| Target signature/body and complete consumer | Byte-identical to base |
| Module header and module docstring | Byte-identical to base |
| Duplication before/after | PASS; identical outputs |
| Style lint | `style_lint: 0 FAIL, 15 WARN over 21 files` |
| New line-length violations | 0 |
| 77-module bootstrap | INCOMPLETE; no module PASS recorded |
| Fresh final sweep | FAILED/INCOMPLETE; first module timed out, exit 124 |
| Owned-file elaboration | FAILED; missing `ClassNP/NTIME.olean` |
| Original 61-check import probe | FAILED; same missing upstream artifact |
| Axiom prints | FAILED; missing `ClassNP/ExhaustiveReplay.olean` |
| Patch/bundle packaging | PASS; bundle's only prerequisite is the base |

The final sweep tail is:

```text
CHECK TCSlib/Complexity/Formulas/CNF
STOP TCSlib/Complexity/Formulas/CNF: exit 124 (124/137 means timeout); no successful sweep claimed.
```

These are infrastructure failures, not passed checks. The source-level freeze
checks do not substitute for elaboration. No claim is made that the requested
warning-set or axiom-print gates were verified locally.

The expected baseline warning inventory, recorded before proof work, is:

```text
TuringMachine/Simulation: 1: branchTM_spaceUsed
TuringMachine/Composition: 3: idTM_computes, ifEqTM_computes, condTM_computes_iff
TuringMachine/Build/Wrappers: 2: timedCondTM_computes, timedCondTM_spaceUsed
TuringMachine/Build/Loop: 5: loopHostTM_contracts, loopHostTM_decides, loopHostTM_finds, loopHostTM_spaceUsed_le_budget, emitLoopTM_computes
TuringMachine/Encoding: 1: pairDiagTM_computes
ClassP/TimeConstructible: 2: _root_.Turing.FinTM.lengthBitsTM_computes, _root_.Turing.FinTM.lengthBitsTM_spaceUsed
TuringMachine/Build/Primitives: 3: polyUnaryTM_spaceUsed, unaryTokenTM_computes, appendBitTM_computes
ClassNP/NDNormalForm: 1: exists_codeNDTM_accepts_linear
ClassNP/ExhaustiveReplay: 1: FinNDTM.exists_exhaustiveDecider
TOTAL 19
```

All 19 baseline admissions remain in source, including the owned one. The
observed warning-set difference is **not established**, because the sweep did
not complete. No other sorry was edited or cited to manufacture a proof.

## Open declaration and continuation

### `Turing.FinNDTM.exists_exhaustiveDecider`

Status: original `sorry`, unchanged. This is the only open declaration in the
owned file. The consumer has no local sorry but still depends on this target.

**Proof sketch.** Use the registered phase host for iterative deepening over the
choice-word length, without assuming the supplied bound is computed. At each
depth enumerate exact-length choice words with the existing increment row;
compose the published replay lemma, R1 silent embedding and step clock. Track
acceptance and liveness in finite control. Between replays perform the bounded
window clear and native-input rewind. Stop at the first all-halting depth.
Acceptance there agrees with acceptance at the supplied bound by monotonicity
and by truncation using `runWith_append` and `runWith_of_halt`. Close the sum of
per-word costs with the docstring's exponential ledger. None of these phases is
claimed implemented by this delivery.

Remaining phases:

1. **Window clear.** Prove a one-step erase-and-move leaf and consume the public
   counter-loop contract. The ordinary word-clear row stops at a blank, whereas
   replay work tapes can have interior blanks; it therefore does not provide the
   required bounded-window effect. Signed sweeps, their support argument, their
   phase composition, and the restart-head discipline still need checking.
2. **One clocked silent replay.** Use only the replay equation and published R1,
   clock and configuration-field equations. Verify both exits and the exact
   captured singleton-output test. Do not unfold the arbitrary NDTM transition.
3. **One depth.** Construct enumeration, finite-control flags, window cleanup,
   rewind and counter preparation through the phase host.
4. **Deepening, answer, ledger.** Prove first-depth termination, agreement of the
   two acceptance bounds, and the machine's actual per-depth cost. No constant
   `C` has been chosen for an executable decider; the final ledger remains open.

Promotion candidates: **none implemented**. The pending bounded-window clear
is the brief's intended promotion candidate. No new shared-host request or
mathematical counterexample was established.

Static edge-case note: the pinned initialization equations make the initial
state `some q₀`. Thus all-branch halting at bound zero is impossible in this
model; that case of the frozen target is vacuous. This observation does not
change the statement, and no new Lean lemma asserting it is delivered. The
zero-work-tape and empty-input cases still require the general construction.

## Axiom walk

The attempted `#print axioms` commands and their actual failure are in
`axioms.log`. There are no new private declarations.

The following is a **source-level dependency walk**, not a successful kernel
axiom print:

```text
Turing.FinNDTM.exists_exhaustiveDecider
  -> its unchanged `sorry`
  -> sorryAx

Turing.ndAcceptsWithin_decider_of_universal
  -> Turing.FinNDTM.exists_exhaustiveDecider
  -> sorryAx
```

No assertion is made about the consumer's complete printed axiom set. The
required absence of `sorryAx` is not satisfied; a complete fill is not claimed.

## Duplication screen

Both runs used the pinned v3 script and six-file population, one run at a time,
under `nice -n 10`. The first run finished before the second began. Each reports
278 declarations, 106 pairs and 36,004 reproduced characters, exactly the pinned
baseline. Both output files have SHA-256
`e5b3bb012bf7d62a73bcc5a6b74ed567e00655287db7e98f7f66e6ecda903c72`.

New cross-file pairs: none. New in-file pairs: none; no justification is needed.
**new copies: none**.

### Before (verbatim)

```text
declarations screened: 278; copy pairs (target reproduces >= half of source): 106; reproduced text: 36,004 chars
   Nondeterminism.lean::e3ChoiceVerifier  reproduces  Nondeterminism.lean::choiceVerifier: 136/136 = 100%
   Nondeterminism.lean::e3_split_spec  reproduces  Nondeterminism.lean::certificateSplit_spec: 125/125 = 100%
   Nondeterminism.lean::certificateSplit_spec  reproduces  Nondeterminism.lean::e3_split_spec: 125/125 = 100%
   Nondeterminism.lean::choiceVerifier  reproduces  Nondeterminism.lean::e3ChoiceVerifier: 136/138 = 99%
   Nondeterminism.lean::choiceVerifier_no_split  reproduces  Nondeterminism.lean::e3_choice_no_split: 145/149 = 97%
   Nondeterminism.lean::certificateSplit_none_iff  reproduces  Nondeterminism.lean::e3_split_none_iff: 155/162 = 96%
   Nondeterminism.lean::e3_choice_append  reproduces  Nondeterminism.lean::choiceVerifier_append: 192/202 = 95%
   Nondeterminism.lean::a2_compile  reproduces  Nondeterminism.lean::b2_compile: 924/975 = 95%
   ChoiceReplay.lean::withChoiceTape  reproduces  StepClock.lean::clockCfg: 157/167 = 94%
   Nondeterminism.lean::choiceVerifier_append  reproduces  Nondeterminism.lean::e3_choice_append: 192/207 = 93%
   Nondeterminism.lean::e3_choice_no_split  reproduces  Nondeterminism.lean::choiceVerifier_no_split: 145/157 = 92%
   Nondeterminism.lean::b2_compile  reproduces  Nondeterminism.lean::a2_compile: 924/1011 = 91%
   CounterLoop.lean::counterLoopTMVia  reproduces  CounterLoop.lean::counterLoopTM: 261/287 = 91%
   Nondeterminism.lean::e3_split_none_iff  reproduces  Nondeterminism.lean::certificateSplit_none_iff: 155/171 = 91%
   Nondeterminism.lean::contSplitWord  reproduces  Nondeterminism.lean::e3SplitWord: 64/71 = 90%
   Nondeterminism.lean::b2_rewind_done  reproduces  Nondeterminism.lean::b2_initial: 263/292 = 90%
   Nondeterminism.lean::cont_choiceVerifier_mem_P  reproduces  Nondeterminism.lean::e3_verifier_of_split: 929/1036 = 90%
   Nondeterminism.lean::cont_parse_double  reproduces  Nondeterminism.lean::cont_parse_separator: 579/652 = 89%
   Nondeterminism.lean::a3n_eq_double  reproduces  Nondeterminism.lean::a3n_eq_separator: 1072/1212 = 88%
   Nondeterminism.lean::choiceCore_step  reproduces  Nondeterminism.lean::choiceCore_finish: 285/324 = 88%
   StepClock.lean::clockCfg  reproduces  ChoiceReplay.lean::withChoiceTape: 157/179 = 88%
   Nondeterminism.lean::e3SplitWord  reproduces  Nondeterminism.lean::contSplitWord: 64/74 = 86%
   Nondeterminism.lean::b2_ready_done  reproduces  Nondeterminism.lean::b2_ready_step: 539/632 = 85%
   Nondeterminism.lean::cont_rewind_choices  reproduces  Nondeterminism.lean::cont_rewind_input: 1256/1488 = 84%
   Nondeterminism.lean::cont_split_answer  reproduces  Nondeterminism.lean::e3_split_answer: 659/784 = 84%
   CounterLoop.lean::counterLoopTM  reproduces  CounterLoop.lean::counterLoopTMVia: 261/311 = 84%
   CounterLoop.lean::counterLoopTM_run_escape  reproduces  CounterLoop.lean::counterLoopTM_run_done: 393/471 = 83%
   Nondeterminism.lean::cont_parse_separator  reproduces  Nondeterminism.lean::cont_parse_double: 579/697 = 83%
   Nondeterminism.lean::a2Borrow_rewind  reproduces  Nondeterminism.lean::a2_load_rewind: 587/708 = 83%
   Nondeterminism.lean::a3n_eq_separator  reproduces  Nondeterminism.lean::a3n_eq_double: 1072/1293 = 83%
   Nondeterminism.lean::a2_load_rewind  reproduces  Nondeterminism.lean::a3n_eq_rewind: 557/687 = 81%
   Nondeterminism.lean::e3_verifier_of_split  reproduces  Nondeterminism.lean::cont_choiceVerifier_mem_P: 929/1146 = 81%
   CounterLoop.lean::counterLoopTMVia_done_segment  reproduces  CounterLoop.lean::counterLoopTMVia_escape_segment: 332/414 = 80%
   Nondeterminism.lean::cont_rewind_input  reproduces  Nondeterminism.lean::cont_rewind_choices: 1256/1596 = 79%
   Nondeterminism.lean::a3n_eq_rewind  reproduces  Nondeterminism.lean::a2_load_rewind: 557/708 = 79%
   Nondeterminism.lean::e3_verifier_of_split  reproduces  Nondeterminism.lean::a3n_comp_at: 342/436 = 78%
   Nondeterminism.lean::cont_choiceVerifier_mem_P  reproduces  Nondeterminism.lean::a3n_comp_at: 342/436 = 78%
   Nondeterminism.lean::a2_exp_scheduler  reproduces  Nondeterminism.lean::a3n_comp_at: 342/436 = 78%
   Nondeterminism.lean::b2_rewind_step  reproduces  Nondeterminism.lean::b2_copy_done: 303/388 = 78%
   Nondeterminism.lean::b2_copy_done  reproduces  Nondeterminism.lean::b2_rewind_step: 303/391 = 77%
   Nondeterminism.lean::b2_host_bound  reproduces  Nondeterminism.lean::a2_host_bound: 381/494 = 77%
   Nondeterminism.lean::b2_ready_run  reproduces  Nondeterminism.lean::b2_rewind_run: 196/256 = 77%
   CounterLoop.lean::counterLoopTMVia_escape_witness  reproduces  CounterLoop.lean::counterLoopTMVia_done_witness: 738/969 = 76%
   CounterLoop.lean::decrementTM_run_succ_ofCfg  reproduces  CounterLoop.lean::counter_complement_twice: 67/88 = 76%
   Nondeterminism.lean::a2_load_rewind  reproduces  Nondeterminism.lean::a2Borrow_rewind: 587/773 = 76%
   Nondeterminism.lean::b2_ready_step  reproduces  Nondeterminism.lean::b2_initial: 221/292 = 76%
   Nondeterminism.lean::b2_guess_return  reproduces  Nondeterminism.lean::b2_initial: 221/292 = 76%
   CounterLoop.lean::RoundContract.counterLoopEscape  reproduces  CounterLoop.lean::RoundContract.counterLoopDone: 1154/1540 = 75%
   Nondeterminism.lean::e3_split_answer  reproduces  Nondeterminism.lean::cont_split_answer: 659/883 = 75%
   Nondeterminism.lean::b2_ready_step  reproduces  Nondeterminism.lean::b2_ready_done: 539/724 = 74%
   CounterLoop.lean::counterLoopTMVia_done_witness  reproduces  CounterLoop.lean::counterLoopTMVia_escape_witness: 738/1008 = 73%
   Nondeterminism.lean::a2Borrow_rewind  reproduces  Nondeterminism.lean::a3n_eq_rewind: 496/687 = 72%
   Nondeterminism.lean::b2_ready_done  reproduces  Nondeterminism.lean::b2_initial: 210/292 = 72%
   CounterLoop.lean::counterLoopTM_run_done  reproduces  CounterLoop.lean::counterLoopTM_run_escape: 393/549 = 72%
   Nondeterminism.lean::choice_certificate_iff  reproduces  Nondeterminism.lean::e3_choice_certificate: 158/222 = 71%
   Nondeterminism.lean::NP_eq_iUnion_NTIME  reproduces  Nondeterminism.lean::NEXP_eq_iUnion_NTIME: 66/93 = 71%
   CounterLoop.lean::decrementTM_run_underflow_ofCfg  reproduces  CounterLoop.lean::counter_complement_twice: 62/88 = 70%
   Nondeterminism.lean::NEXP_eq_iUnion_NTIME  reproduces  Nondeterminism.lean::NP_eq_iUnion_NTIME: 66/94 = 70%
   Nondeterminism.lean::a3n_scaled_envelope  reproduces  Nondeterminism.lean::a2_envelope: 535/766 = 70%
   Nondeterminism.lean::cont_start_core  reproduces  Nondeterminism.lean::cont_write_apply: 221/320 = 69%
   Nondeterminism.lean::cont_parse_run  reproduces  Nondeterminism.lean::a3n_eq_parse: 350/512 = 68%
   CounterLoop.lean::RoundContract.counterLoopDone  reproduces  CounterLoop.lean::RoundContract.counterLoopEscape: 1180/1750 = 67%
   CounterLoop.lean::counterLoopTMVia_escape_segment  reproduces  CounterLoop.lean::counterLoopTMVia_done_segment: 332/499 = 67%
   Nondeterminism.lean::b2_guess_run  reproduces  Nondeterminism.lean::cont_guess_run: 151/227 = 67%
   Nondeterminism.lean::b2_rewind_run  reproduces  Nondeterminism.lean::b2_ready_run: 196/295 = 66%
   Nondeterminism.lean::e3_choice_certificate  reproduces  Nondeterminism.lean::choice_certificate_iff: 158/239 = 66%
   StepClock.lean::sc_clockTM  reproduces  CounterLoop.lean::counterLoopTMVia: 205/311 = 66%
   Nondeterminism.lean::e3ChoiceVerifier  reproduces  NTIME.lean::AcceptsWithin: 71/109 = 65%
   Nondeterminism.lean::choiceVerifier  reproduces  NTIME.lean::AcceptsWithin: 71/109 = 65%
   Nondeterminism.lean::a2_host_bound  reproduces  Nondeterminism.lean::b2_host_bound: 381/588 = 65%
   CounterLoop.lean::RoundContract.counterLoopDone_traj  reproduces  CounterLoop.lean::RoundContract.counterLoopEscape_traj: 343/533 = 64%
   Nondeterminism.lean::cont_split_length  reproduces  Nondeterminism.lean::e3_split_length: 90/140 = 64%
   Nondeterminism.lean::a3n_eq_rewind  reproduces  Nondeterminism.lean::a2Borrow_rewind: 496/773 = 64%
   Nondeterminism.lean::e3c_bits_injective  reproduces  Nondeterminism.lean::a2Value_bits: 84/131 = 64%
   Nondeterminism.lean::cont_rewind_input  reproduces  Nondeterminism.lean::cont_write_apply: 205/320 = 64%
   Nondeterminism.lean::cont_rewind_choices  reproduces  Nondeterminism.lean::cont_write_apply: 205/320 = 64%
   CounterLoop.lean::counterWord_value  reproduces  CounterLoop.lean::counter_word_decrement: 94/150 = 63%
   CounterLoop.lean::RoundContract.counterLoopEscape_traj  reproduces  CounterLoop.lean::RoundContract.counterLoopDone_traj: 343/555 = 62%
   Nondeterminism.lean::b2_copy_step  reproduces  Nondeterminism.lean::a2_copy_step: 325/529 = 61%
   Nondeterminism.lean::cont_mask_count  reproduces  Nondeterminism.lean::b2_unary_run: 81/135 = 60%
   CounterLoop.lean::decrementTM_run_succ_ofCfg  reproduces  CounterLoop.lean::decrementTM_run_underflow_ofCfg: 448/750 = 60%
   Nondeterminism.lean::NP_subset_iUnion_NTIME  reproduces  Nondeterminism.lean::NEXP_subset_iUnion_NTIME: 62/106 = 58%
   Nondeterminism.lean::a2_envelope  reproduces  Nondeterminism.lean::a3n_scaled_envelope: 535/929 = 58%
   Nondeterminism.lean::cont_split_answer  reproduces  Nondeterminism.lean::cont_split_length: 110/192 = 57%
   Nondeterminism.lean::choiceCore_step  reproduces  Nondeterminism.lean::cont_write_apply: 183/320 = 57%
   Nondeterminism.lean::a3n_eq_parse  reproduces  Nondeterminism.lean::cont_parse_run: 350/626 = 56%
   CounterLoop.lean::counterLoopTMVia  reproduces  StepClock.lean::sc_clockTM: 205/369 = 56%
   Nondeterminism.lean::NEXP_subset_iUnion_NTIME  reproduces  Nondeterminism.lean::NP_subset_iUnion_NTIME: 62/114 = 54%
   Nondeterminism.lean::b2_rewind_done  reproduces  Nondeterminism.lean::b2_ready_done: 393/724 = 54%
   Nondeterminism.lean::b2_rewind_done  reproduces  Nondeterminism.lean::b2_guess_return: 316/590 = 54%
   Nondeterminism.lean::b2_ready_step  reproduces  Nondeterminism.lean::b2_guess_return: 314/590 = 53%
   Nondeterminism.lean::a3n_eq_rewind  reproduces  Nondeterminism.lean::b2_unary_run: 71/135 = 53%
   Nondeterminism.lean::a2_load_rewind  reproduces  Nondeterminism.lean::b2_unary_run: 71/135 = 53%
   NTIME.lean::AcceptsWithin  reproduces  Nondeterminism.lean::choiceVerifier: 71/136 = 52%
   Nondeterminism.lean::cont_rewind_input  reproduces  Nondeterminism.lean::b2_unary_run: 70/135 = 52%
   Nondeterminism.lean::cont_rewind_choices  reproduces  Nondeterminism.lean::b2_unary_run: 70/135 = 52%
   Nondeterminism.lean::a2Borrow_run  reproduces  Nondeterminism.lean::b2_unary_run: 70/135 = 52%
   Nondeterminism.lean::b2_verify_step  reproduces  Nondeterminism.lean::b2_ready_step: 327/632 = 52%
   NTIME.lean::AcceptsWithin  reproduces  Nondeterminism.lean::e3ChoiceVerifier: 71/138 = 51%
   Nondeterminism.lean::b2_copy_step  reproduces  Nondeterminism.lean::b2_rewind_step: 201/391 = 51%
   Nondeterminism.lean::a3n_eq_separator  reproduces  Nondeterminism.lean::b2_unary_run: 69/135 = 51%
   Nondeterminism.lean::a3n_eq_double  reproduces  Nondeterminism.lean::b2_unary_run: 69/135 = 51%
   Nondeterminism.lean::a2Borrow_rewind  reproduces  Nondeterminism.lean::b2_unary_run: 69/135 = 51%
   Nondeterminism.lean::cont_rewind_input  reproduces  Nondeterminism.lean::cont_start_core: 432/858 = 50%
   Nondeterminism.lean::cont_rewind_choices  reproduces  Nondeterminism.lean::cont_start_core: 432/858 = 50%
   Nondeterminism.lean::e3_loop_result  reproduces  Nondeterminism.lean::e3_split_length: 70/140 = 50%
```

### After (verbatim)

```text
declarations screened: 278; copy pairs (target reproduces >= half of source): 106; reproduced text: 36,004 chars
   Nondeterminism.lean::e3ChoiceVerifier  reproduces  Nondeterminism.lean::choiceVerifier: 136/136 = 100%
   Nondeterminism.lean::e3_split_spec  reproduces  Nondeterminism.lean::certificateSplit_spec: 125/125 = 100%
   Nondeterminism.lean::certificateSplit_spec  reproduces  Nondeterminism.lean::e3_split_spec: 125/125 = 100%
   Nondeterminism.lean::choiceVerifier  reproduces  Nondeterminism.lean::e3ChoiceVerifier: 136/138 = 99%
   Nondeterminism.lean::choiceVerifier_no_split  reproduces  Nondeterminism.lean::e3_choice_no_split: 145/149 = 97%
   Nondeterminism.lean::certificateSplit_none_iff  reproduces  Nondeterminism.lean::e3_split_none_iff: 155/162 = 96%
   Nondeterminism.lean::e3_choice_append  reproduces  Nondeterminism.lean::choiceVerifier_append: 192/202 = 95%
   Nondeterminism.lean::a2_compile  reproduces  Nondeterminism.lean::b2_compile: 924/975 = 95%
   ChoiceReplay.lean::withChoiceTape  reproduces  StepClock.lean::clockCfg: 157/167 = 94%
   Nondeterminism.lean::choiceVerifier_append  reproduces  Nondeterminism.lean::e3_choice_append: 192/207 = 93%
   Nondeterminism.lean::e3_choice_no_split  reproduces  Nondeterminism.lean::choiceVerifier_no_split: 145/157 = 92%
   Nondeterminism.lean::b2_compile  reproduces  Nondeterminism.lean::a2_compile: 924/1011 = 91%
   CounterLoop.lean::counterLoopTMVia  reproduces  CounterLoop.lean::counterLoopTM: 261/287 = 91%
   Nondeterminism.lean::e3_split_none_iff  reproduces  Nondeterminism.lean::certificateSplit_none_iff: 155/171 = 91%
   Nondeterminism.lean::contSplitWord  reproduces  Nondeterminism.lean::e3SplitWord: 64/71 = 90%
   Nondeterminism.lean::b2_rewind_done  reproduces  Nondeterminism.lean::b2_initial: 263/292 = 90%
   Nondeterminism.lean::cont_choiceVerifier_mem_P  reproduces  Nondeterminism.lean::e3_verifier_of_split: 929/1036 = 90%
   Nondeterminism.lean::cont_parse_double  reproduces  Nondeterminism.lean::cont_parse_separator: 579/652 = 89%
   Nondeterminism.lean::a3n_eq_double  reproduces  Nondeterminism.lean::a3n_eq_separator: 1072/1212 = 88%
   Nondeterminism.lean::choiceCore_step  reproduces  Nondeterminism.lean::choiceCore_finish: 285/324 = 88%
   StepClock.lean::clockCfg  reproduces  ChoiceReplay.lean::withChoiceTape: 157/179 = 88%
   Nondeterminism.lean::e3SplitWord  reproduces  Nondeterminism.lean::contSplitWord: 64/74 = 86%
   Nondeterminism.lean::b2_ready_done  reproduces  Nondeterminism.lean::b2_ready_step: 539/632 = 85%
   Nondeterminism.lean::cont_rewind_choices  reproduces  Nondeterminism.lean::cont_rewind_input: 1256/1488 = 84%
   Nondeterminism.lean::cont_split_answer  reproduces  Nondeterminism.lean::e3_split_answer: 659/784 = 84%
   CounterLoop.lean::counterLoopTM  reproduces  CounterLoop.lean::counterLoopTMVia: 261/311 = 84%
   CounterLoop.lean::counterLoopTM_run_escape  reproduces  CounterLoop.lean::counterLoopTM_run_done: 393/471 = 83%
   Nondeterminism.lean::cont_parse_separator  reproduces  Nondeterminism.lean::cont_parse_double: 579/697 = 83%
   Nondeterminism.lean::a2Borrow_rewind  reproduces  Nondeterminism.lean::a2_load_rewind: 587/708 = 83%
   Nondeterminism.lean::a3n_eq_separator  reproduces  Nondeterminism.lean::a3n_eq_double: 1072/1293 = 83%
   Nondeterminism.lean::a2_load_rewind  reproduces  Nondeterminism.lean::a3n_eq_rewind: 557/687 = 81%
   Nondeterminism.lean::e3_verifier_of_split  reproduces  Nondeterminism.lean::cont_choiceVerifier_mem_P: 929/1146 = 81%
   CounterLoop.lean::counterLoopTMVia_done_segment  reproduces  CounterLoop.lean::counterLoopTMVia_escape_segment: 332/414 = 80%
   Nondeterminism.lean::cont_rewind_input  reproduces  Nondeterminism.lean::cont_rewind_choices: 1256/1596 = 79%
   Nondeterminism.lean::a3n_eq_rewind  reproduces  Nondeterminism.lean::a2_load_rewind: 557/708 = 79%
   Nondeterminism.lean::e3_verifier_of_split  reproduces  Nondeterminism.lean::a3n_comp_at: 342/436 = 78%
   Nondeterminism.lean::cont_choiceVerifier_mem_P  reproduces  Nondeterminism.lean::a3n_comp_at: 342/436 = 78%
   Nondeterminism.lean::a2_exp_scheduler  reproduces  Nondeterminism.lean::a3n_comp_at: 342/436 = 78%
   Nondeterminism.lean::b2_rewind_step  reproduces  Nondeterminism.lean::b2_copy_done: 303/388 = 78%
   Nondeterminism.lean::b2_copy_done  reproduces  Nondeterminism.lean::b2_rewind_step: 303/391 = 77%
   Nondeterminism.lean::b2_host_bound  reproduces  Nondeterminism.lean::a2_host_bound: 381/494 = 77%
   Nondeterminism.lean::b2_ready_run  reproduces  Nondeterminism.lean::b2_rewind_run: 196/256 = 77%
   CounterLoop.lean::counterLoopTMVia_escape_witness  reproduces  CounterLoop.lean::counterLoopTMVia_done_witness: 738/969 = 76%
   CounterLoop.lean::decrementTM_run_succ_ofCfg  reproduces  CounterLoop.lean::counter_complement_twice: 67/88 = 76%
   Nondeterminism.lean::a2_load_rewind  reproduces  Nondeterminism.lean::a2Borrow_rewind: 587/773 = 76%
   Nondeterminism.lean::b2_ready_step  reproduces  Nondeterminism.lean::b2_initial: 221/292 = 76%
   Nondeterminism.lean::b2_guess_return  reproduces  Nondeterminism.lean::b2_initial: 221/292 = 76%
   CounterLoop.lean::RoundContract.counterLoopEscape  reproduces  CounterLoop.lean::RoundContract.counterLoopDone: 1154/1540 = 75%
   Nondeterminism.lean::e3_split_answer  reproduces  Nondeterminism.lean::cont_split_answer: 659/883 = 75%
   Nondeterminism.lean::b2_ready_step  reproduces  Nondeterminism.lean::b2_ready_done: 539/724 = 74%
   CounterLoop.lean::counterLoopTMVia_done_witness  reproduces  CounterLoop.lean::counterLoopTMVia_escape_witness: 738/1008 = 73%
   Nondeterminism.lean::a2Borrow_rewind  reproduces  Nondeterminism.lean::a3n_eq_rewind: 496/687 = 72%
   Nondeterminism.lean::b2_ready_done  reproduces  Nondeterminism.lean::b2_initial: 210/292 = 72%
   CounterLoop.lean::counterLoopTM_run_done  reproduces  CounterLoop.lean::counterLoopTM_run_escape: 393/549 = 72%
   Nondeterminism.lean::choice_certificate_iff  reproduces  Nondeterminism.lean::e3_choice_certificate: 158/222 = 71%
   Nondeterminism.lean::NP_eq_iUnion_NTIME  reproduces  Nondeterminism.lean::NEXP_eq_iUnion_NTIME: 66/93 = 71%
   CounterLoop.lean::decrementTM_run_underflow_ofCfg  reproduces  CounterLoop.lean::counter_complement_twice: 62/88 = 70%
   Nondeterminism.lean::NEXP_eq_iUnion_NTIME  reproduces  Nondeterminism.lean::NP_eq_iUnion_NTIME: 66/94 = 70%
   Nondeterminism.lean::a3n_scaled_envelope  reproduces  Nondeterminism.lean::a2_envelope: 535/766 = 70%
   Nondeterminism.lean::cont_start_core  reproduces  Nondeterminism.lean::cont_write_apply: 221/320 = 69%
   Nondeterminism.lean::cont_parse_run  reproduces  Nondeterminism.lean::a3n_eq_parse: 350/512 = 68%
   CounterLoop.lean::RoundContract.counterLoopDone  reproduces  CounterLoop.lean::RoundContract.counterLoopEscape: 1180/1750 = 67%
   CounterLoop.lean::counterLoopTMVia_escape_segment  reproduces  CounterLoop.lean::counterLoopTMVia_done_segment: 332/499 = 67%
   Nondeterminism.lean::b2_guess_run  reproduces  Nondeterminism.lean::cont_guess_run: 151/227 = 67%
   Nondeterminism.lean::b2_rewind_run  reproduces  Nondeterminism.lean::b2_ready_run: 196/295 = 66%
   Nondeterminism.lean::e3_choice_certificate  reproduces  Nondeterminism.lean::choice_certificate_iff: 158/239 = 66%
   StepClock.lean::sc_clockTM  reproduces  CounterLoop.lean::counterLoopTMVia: 205/311 = 66%
   Nondeterminism.lean::e3ChoiceVerifier  reproduces  NTIME.lean::AcceptsWithin: 71/109 = 65%
   Nondeterminism.lean::choiceVerifier  reproduces  NTIME.lean::AcceptsWithin: 71/109 = 65%
   Nondeterminism.lean::a2_host_bound  reproduces  Nondeterminism.lean::b2_host_bound: 381/588 = 65%
   CounterLoop.lean::RoundContract.counterLoopDone_traj  reproduces  CounterLoop.lean::RoundContract.counterLoopEscape_traj: 343/533 = 64%
   Nondeterminism.lean::cont_split_length  reproduces  Nondeterminism.lean::e3_split_length: 90/140 = 64%
   Nondeterminism.lean::a3n_eq_rewind  reproduces  Nondeterminism.lean::a2Borrow_rewind: 496/773 = 64%
   Nondeterminism.lean::e3c_bits_injective  reproduces  Nondeterminism.lean::a2Value_bits: 84/131 = 64%
   Nondeterminism.lean::cont_rewind_input  reproduces  Nondeterminism.lean::cont_write_apply: 205/320 = 64%
   Nondeterminism.lean::cont_rewind_choices  reproduces  Nondeterminism.lean::cont_write_apply: 205/320 = 64%
   CounterLoop.lean::counterWord_value  reproduces  CounterLoop.lean::counter_word_decrement: 94/150 = 63%
   CounterLoop.lean::RoundContract.counterLoopEscape_traj  reproduces  CounterLoop.lean::RoundContract.counterLoopDone_traj: 343/555 = 62%
   Nondeterminism.lean::b2_copy_step  reproduces  Nondeterminism.lean::a2_copy_step: 325/529 = 61%
   Nondeterminism.lean::cont_mask_count  reproduces  Nondeterminism.lean::b2_unary_run: 81/135 = 60%
   CounterLoop.lean::decrementTM_run_succ_ofCfg  reproduces  CounterLoop.lean::decrementTM_run_underflow_ofCfg: 448/750 = 60%
   Nondeterminism.lean::NP_subset_iUnion_NTIME  reproduces  Nondeterminism.lean::NEXP_subset_iUnion_NTIME: 62/106 = 58%
   Nondeterminism.lean::a2_envelope  reproduces  Nondeterminism.lean::a3n_scaled_envelope: 535/929 = 58%
   Nondeterminism.lean::cont_split_answer  reproduces  Nondeterminism.lean::cont_split_length: 110/192 = 57%
   Nondeterminism.lean::choiceCore_step  reproduces  Nondeterminism.lean::cont_write_apply: 183/320 = 57%
   Nondeterminism.lean::a3n_eq_parse  reproduces  Nondeterminism.lean::cont_parse_run: 350/626 = 56%
   CounterLoop.lean::counterLoopTMVia  reproduces  StepClock.lean::sc_clockTM: 205/369 = 56%
   Nondeterminism.lean::NEXP_subset_iUnion_NTIME  reproduces  Nondeterminism.lean::NP_subset_iUnion_NTIME: 62/114 = 54%
   Nondeterminism.lean::b2_rewind_done  reproduces  Nondeterminism.lean::b2_ready_done: 393/724 = 54%
   Nondeterminism.lean::b2_rewind_done  reproduces  Nondeterminism.lean::b2_guess_return: 316/590 = 54%
   Nondeterminism.lean::b2_ready_step  reproduces  Nondeterminism.lean::b2_guess_return: 314/590 = 53%
   Nondeterminism.lean::a3n_eq_rewind  reproduces  Nondeterminism.lean::b2_unary_run: 71/135 = 53%
   Nondeterminism.lean::a2_load_rewind  reproduces  Nondeterminism.lean::b2_unary_run: 71/135 = 53%
   NTIME.lean::AcceptsWithin  reproduces  Nondeterminism.lean::choiceVerifier: 71/136 = 52%
   Nondeterminism.lean::cont_rewind_input  reproduces  Nondeterminism.lean::b2_unary_run: 70/135 = 52%
   Nondeterminism.lean::cont_rewind_choices  reproduces  Nondeterminism.lean::b2_unary_run: 70/135 = 52%
   Nondeterminism.lean::a2Borrow_run  reproduces  Nondeterminism.lean::b2_unary_run: 70/135 = 52%
   Nondeterminism.lean::b2_verify_step  reproduces  Nondeterminism.lean::b2_ready_step: 327/632 = 52%
   NTIME.lean::AcceptsWithin  reproduces  Nondeterminism.lean::e3ChoiceVerifier: 71/138 = 51%
   Nondeterminism.lean::b2_copy_step  reproduces  Nondeterminism.lean::b2_rewind_step: 201/391 = 51%
   Nondeterminism.lean::a3n_eq_separator  reproduces  Nondeterminism.lean::b2_unary_run: 69/135 = 51%
   Nondeterminism.lean::a3n_eq_double  reproduces  Nondeterminism.lean::b2_unary_run: 69/135 = 51%
   Nondeterminism.lean::a2Borrow_rewind  reproduces  Nondeterminism.lean::b2_unary_run: 69/135 = 51%
   Nondeterminism.lean::cont_rewind_input  reproduces  Nondeterminism.lean::cont_start_core: 432/858 = 50%
   Nondeterminism.lean::cont_rewind_choices  reproduces  Nondeterminism.lean::cont_start_core: 432/858 = 50%
   Nondeterminism.lean::e3_loop_result  reproduces  Nondeterminism.lean::e3_split_length: 70/140 = 50%
```

## Archive contents

- This `REPORT.md`.
- Full modified `TCSlib/Complexity/ClassNP/ExhaustiveReplay.lean`.
- One `git format-patch` patch against the exact base, under `patches/`.
- `c1-exhaustive.bundle`, with the base as its only prerequisite.
- `bootstrap.log`, `final-sweep.log`, and `axioms.log`, including actual failures.
- `screen-before.txt` and `screen-after.txt`.
- The addendum-required `evidence/runtime/executable-path.c` source only.
- `SHA256SUMS`, covering every other archive member.

No compiled runtime, olean, dependency cache, input attachment, or unverified
proof draft is included. The archive is an incomplete continuation record and
must not be accepted as a completed fill.
