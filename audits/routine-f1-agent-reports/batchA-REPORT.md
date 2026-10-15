# §12 F1 Batch A — proof-fill report

**Complete: 13/13 targets proved.** No admitted helper or admitted dependency.
Only `TCSlib/Complexity/TuringMachine/Build/Embed.lean` changed in the git series.
No push or PR was made.

Repository: `https://github.com/Shilun-Allan-Li/tcslib`.
Base branch: `complexity/arora-barak-ch3-4`.
Base commit: `42d524b665f1fc856fe6f60a27a7d7ecced91b71`.
Working branch: `fill/s12-f1-A`.
Delivered commit: `6983c4e7657871cec5f47b0f23978f94250586dd`.

The followed brief is `briefs/routine-f1-batchA.md` from this base. The base
is the brief-publication commit immediately after its cited `f7f4f0f7`;
no rebase occurred. The three audit reports and resolutions were read.

## Target completion, in the required fill order

| Order | Target in namespace `Turing` | Result |
|---:|---|---|
| 1 | `embedSilentTM_runFrom` | Proved |
| 2 | `embedSilentTM_frame` | Proved |
| 3 | `embedSilentTM_visitedByTapeHead` | Proved |
| 4 | `embedSilentTM_visitedByTapeHead_frame` | Proved |
| 5 | `embedSilentTM_spaceUsedByTape_cap` | Proved |
| 6 | `embedEmitTM_runFrom` | Proved |
| 7 | `embedEmitTM_frame` | Proved |
| 8 | `embedEmitTM_visitedByTapeHead` | Proved |
| 9 | `embedEmitTM_visitedByTapeHead_frame` | Proved |
| 10 | `embedSilentRetTM_run` | Proved |
| 11 | `embedEmitRetTM_run` | Proved |
| 12 | `embedSilentRetTM_visitedByTapeHead` | Proved |
| 13 | `embedEmitRetTM_visitedByTapeHead` | Proved |

The first nine proofs use the two inverse-selection lemmas and the two
componentwise action/step commutations. The capture bound uses output
monotonicity to contain the head trajectory in the integer interval between
its initial and final positions, then takes the interval cardinality.

The two returning-run proofs instantiate `embedThroughHalt`, which follows
the binding audit plan: derive positive time, induct over the live prefix,
execute the final source action from the predecessor time, and exclude the
right anchor at all earlier times. `embedSilentRet_step` and
`embedEmitRet_step` identify the audit's complete-action component check;
`embedReturnAction` and `embedReturnCfg_live` expose the optional-successor
cases without changing any non-control field.

The last two proofs use `embedReturn_visited` directly. They do **not**
depend on either returning-run contract. This helper compares the host
machines, treats initially halted starts separately, and imposes no source
termination or capture-separation hypothesis. The one-step S8 observations
for both flavors also check using only `rfl`; see `SanityCheck.lean` and
`sanity.log`.

## Every new source declaration

All 14 additions to `Embed.lean` are `private`; 12 are lemmas and 2 are definitions.
There are no new public declarations, instances, axioms, or removals.

| Private declaration | Role |
|---|---|
| `embedSlot_selected` | Unique inverse on a selected tape. |
| `embedSlot_unselected` | No inverse outside the selected bank. |
| `embedSilent_apply` | Silent action transport, component by component, including buffer append. |
| `embedSilent_step` | Source reads and complete silent step commutation. |
| `embedEmit_apply` | Forwarding action transport and output append associativity. |
| `embedEmit_step` | Source reads and complete forwarding step commutation. |
| `embedReturnAction` | Private action encoding that changes only the successor control. |
| `embedReturnCfg` | Private configuration encoding that changes only the control. |
| `embedReturnCfg_live` | Agreement of the return encoding with left state mapping at a live state. |
| `embedReturn_step` | Direct closed-host/returning-host one-step comparison, including stationary halt/anchor. |
| `embedSilentRet_step` | Audit step 3 for the silent returning transport. |
| `embedThroughHalt` | Audit positive-time argument, live-prefix induction, last step, and first-visit exclusion. |
| `embedEmitRet_step` | Audit step 3 for the forwarding returning transport. |
| `embedReturn_visited` | All-time direct host comparison of visited sets; initially halted starts handled separately. |

The separate `SanityCheck.lean` contains three private test fixtures
(`emitHalt`, `emptyBank`, `silentStart`) and two anonymous `example`s.
These are not repository changes or public library declarations.

**Requested shared lemmas:** none. **Escalations:** none.

## Freeze and documentation

`freeze-check.json` records a comment-stripped comparison with the base:
all 21 original declarations remain in their original order; all signatures
are unchanged; all eight original definitions, including the two original
private definitions, are unchanged. The only modified theorem bodies are
the 13 commissioned targets. Imports and options are unchanged.

Two permitted proof-sketch appendices were added: the capture bound's
interval-containment shortcut, and the returning silent visited-set proof's
independence from the through-halt contracts. No attribution was edited.
Existing skeleton-status wording was retained under the brief's freeze.
The file stays a single coherent cluster because this batch's exclusive
ownership forbids moving helpers into other modules.

## Verification

- Final `Embed` check: exit 0; a fresh `.olean`; zero `error:` diagnostics;
  zero `declaration uses 'sorry'` warnings. See `sweep.log`.
- All 13 final `#print axioms` results are in `axioms.log`, generated by
  `AxiomCheck.lean` against the fresh tree. Every footprint is a subset of
  `[propext, Classical.choice, Quot.sound]`; `sorryAx` never appears.
- S8 definitional checks: exit 0, no diagnostics (`sanity.log`).
- Frozen-surface comparison: passed. `git diff --check`: passed.
- The patch was independently applied to the recorded base file and
  reproduced the final source byte-for-byte. The incremental git bundle
  verifies and records the base as its prerequisite (`bundle-verify.log`).
- The bootstrap completed all 65 listed modules after checking the six
  additional imports described below. The continuation has zero errors.
  The final fresh Turing-machine facade check exited 0 with no diagnostics;
  its command and status are appended to `sweep.log`.

The only final source warnings are unused `hcap` parameters in
`embedSilentTM_runFrom` and `embedSilentRetTM_run`. Their audited signatures
are preserved. The private transport equations actually hold even when
capture is selected: both definitions then give selected-tape behavior
priority and ignore capture. The off-bank premise remains essential to
the exported capture-tape interpretation and space bound, where it is used.

Final per-file log tail:

```text
warning: unused variable `hcap` (embedSilentTM_runFrom)
warning: unused variable `hcap` (embedSilentRetTM_run)
Exit status: 0
Command: bash scripts/lean_check_tree.sh TCSlib/Complexity/TuringMachine
Exit status: 0
```

## Environment and reproducibility

Lean is the unmodified official 4.25.0 release
(`cdd38ac5115bdeec5f609e9126cce00f51ae88b3`); mathlib is the pinned
`029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e`.
The standard `lake exe cache get` setup failed during its optional
ProofWidgets release fetch. Subsequent setup called the pinned cache
library's download/unpack functions for the required imports, without
editing dependency sources. No campaign `lake build` was issued.

This execution environment permits `/proc/self/exe` but rejects the
numerical spelling of the current process's executable path. A small
runtime path-compatibility shim maps only that exact own-process spelling
to `/proc/self/exe`. It changes no Lean code, kernel operation, source,
proof, or imported declaration. Normal environments do not need it.

The prescribed 65-module bootstrap list predates six imports. The first
pass additionally checked `Build/Embed`, `Build/Seam`, `Build/Catalog`, and
`NDCodes` before the Turing-machine facade, which passed. It subsequently
stopped at the separate `Formulas` facade because `QBF.olean` was missing.
The continuation checks the unchanged `QBF` and `QBFEncoding` modules,
then resumes at `Formulas`. The original missing-dependency diagnostic is
retained in `bootstrap.log`; continuation evidence is in
`bootstrap-resume.log`. No dependency source was changed. All repository
checks use `scripts/lean_check_tree.sh` and direct Lean checks.

To integrate with the recorded base available:

```sh
git am -3 patches/*.patch
```

Then use the repository check script on `Build/Embed` and the facade,
and run `AxiomCheck.lean` against that fresh olean tree. `changes.bundle`
is an alternative git transport with the same single source commit.
`SHA256SUMS` covers every delivered file except the checksum manifest itself.
