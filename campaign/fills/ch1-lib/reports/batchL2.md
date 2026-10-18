# Batch L2 — completed loop-controller fill

**Complete.** `Turing.FinTM.loopHost_contracts` is proved. The owned file has
zero `sorry` tokens. All four public loop theorems are admission-free, as are
all 95 private helpers. No continuation frontier remains.

## Provenance and scope

- Repository: https://github.com/Shilun-Allan-Li/tcslib
- Required campaign branch: `complexity/arora-barak-ch1`, explicitly cloned with `--single-branch --branch`.
- Required base: `90273dd6dea2f9e092ca7d4b5ab5dc72c96ef1ee`.
- Brief read from campaign tip `646b9ee6b482867cb588a67f3014dcc00ebac7d5`; its required base was then selected.
- Local working branch, as prescribed by the brief: `fill/lib-L2`.
- Completion commit: `2f40ca5fde2a71770fdd943c81ff337f34e6cd1d`.
- Execution: `lib-L2-20261003T213754Z`.
- Only changed tracked file: `TCSlib/Complexity/TuringMachine/Build/Loop.lean`.
- No push or PR; no other branch was modified. Delivery is this ZIP.

Read and followed: the L2 brief, original L brief, predecessor continuation
and report ledger, workflow §§4/6, policy, W environment protocol, epoch-1
pitfalls, and the audited construction ledger. The predecessor's ordered
obligations were worked in order; no machine definition or existing signature
was changed. The extra verification files live only in this delivery directory.

## Six obligations and construction ledger

| Obligation | Discharging declarations and result |
| --- | --- |
| 1. Relocations and fuel setup, phases 0–3 | `loopFuel_run` uses `rightCfg_run` twice; `loopFuel_init` identifies the genuine start. `loopHost_fuel_rewind`, `loopHost_fuel_copy`, `loopHost_fuel_return`, and `loopHost_fuel_setup` prove exact setup scans. `loopHost_prepare` chooses the first fuel halt, uses the actual-host capture helper, retains fuel residue, and connects the checked input rewind to the source displacement bound. |
| 2. Startup return and active body calls | `loopBodySource_run` uses `leftCfg_run`. `loopHost_anchor_return` supplies the silent false-flag stop; `loopReady_call`, `loopHost_release`, and `loopHost_start` assemble startup. `loopHost_halt_return` captures the first genuine halt and its full emission. Startup uses the no-anchor guard including time zero; active calls use the release bit and strict-interior guard. |
| 3. Counter lifting, phases 8–10 | `loopHost_borrow_step`, `loopHost_borrow_run`, `loopHost_borrow_rewind`, and `loopHost_borrow` prove the counter operation in the actual host against arbitrary preserved residue. `loopHost_reject` clears the flag and includes phase 11's exhaustion emission in the rejecting segment. The bound is worst-case width, never amortization. |
| 4. Acceptance completion, phases 7/12/13 | `loopHost_payload_rewind` proves phase 12. `loopHost_frame_replay` applies the existing `loopHost_replay`. `loopHost_accept` dispatches by the true flag independently of payload length; `loopHost_round` charges output length to elapsed body time via `loop_output_length_le`. |
| 5. Canonical configuration family | Inside `loopHost_contracts`, `words` is the debit iterate of the initial binary fuel and `orbit` is the body-state iterate. `candidate` uses `Cfg.ofWords` and `loopCall` with blank flag/capture, released active control, and the same completed fuel residue. The existing width/value lemmas and `loop_orbit_inv` supply each local round contract, including unreachable seams after earlier acceptance. |
| 6. Terminal and single constant | The main proof fixes one time witness per candidate. For a rejecting last candidate, `terminal` is its actual completed underflow/emission endpoint. For an accepting last candidate, it is an arbitrary halted configuration with the required false/empty output. `cfg` selects candidates up to the fuel value and that terminal afterwards. `loopHost_bound = max 1 (max 9 (3 + 2 + 5)) = 10` is the single exported coefficient. |

The 14-phase table is fully discharged: phases 0/1 by fuel setup/rewind;
2 by fuel copy; 3 by fuel return; 4/5 by the inherited input rewind inside
`loopHost_prepare`; 6 by release/start; 7 by reject/accept; 8 by borrow
step/run; 9/10 by borrow rewind; 11 by reject; 12 by payload rewind; and
13 by frame replay through the inherited actual-host replay lemma.

All construction helpers have empty admission-root sets. The body-capture
and fuel-capture helpers now depend on the integrated, proved `Turing.capture_run`.
The existing corollary proofs were left unchanged: `loop_halted_run` handles
the decision terminal, and `loop_find_run` supplies the exact first payload.
No application of frozen `loop_run` to a `[false]` terminal was introduced.

## Checked time ledger

The following calculations are formalized in the indicated lemmas. Each body
round duration is at most `T x.length`, and every retained counter width is
at most `T x.length`.

| Component | Bound |
| --- | --- |
| Fuel rewind/copy/return, including the first left move | `1 + (word.length + 1) + (word.length + 1) + (word.length + 1) = 3 * word.length + 4` |
| Input rewind after fuel | At most `fuel.inputPos.val + 2`, and the source input position is at most `1 + firstHaltTime`. |
| Prepared startup | `firstHaltTime + 3 * fuel.output.length + 4 + rewindTime ≤ 5 * T x.length + 7` |
| Body startup and release | `btime + 2 ≤ T x.length + 2` |
| Complete startup | `(5 * T x.length + 7) + (T x.length + 2) = 6 * T x.length + 9 ≤ 9 * (T x.length + 1)` |
| Counter, including underflow rewind | `2 * loopBorrowPos word + 2 ≤ 2 * word.length + 2` |
| Rejecting return dispatch, counter, and possible final emission | At most `2 * word.length + 4` |
| Accepting return dispatch/replay | At most `2 * c.output.length + 3`, including an empty payload |
| Entire local body/controller segment | At most `3 * t + 2 * word.length + 5`, hence at most the audit ledger's `(3 + 2 + 5) * (T x.length + 1)` |

The maximum of one, startup coefficient nine, and segment coefficient ten
is ten. The proof includes zero fuel and width zero through the same formulas:
startup performs no debit, so candidate zero is tested before the first underflow.

## Freeze and admissions

`verification/freeze.py` verifies:

- All 60 pre-existing declaration signatures and their order are unchanged,
  including the private `loopHost_contracts` interface.
- All five public declarations are preserved, with no public gains or losses.
- All 17 pre-existing definitions/abbreviations, including the controller,
  are unchanged after comment stripping and whitespace normalization.
- All 60 pre-existing declaration docstrings remain verbatim.
- The module docstring has only an appended completion paragraph; a separate
  ordinary comment marks the old private continuation docstring as historical.
- Forty new declarations are private; no import was added.
- Only the owned source differs from the required base, and it has zero admissions.

The updated `verification/Axioms.lean` sets **every** expected root set to
empty, including the three combinators, `loopHost_contracts`, and the three
capture helpers. It checks the four public loop targets, all 95 private
helpers, and `Turing.capture_run`: **100 checks**. The kernel walk traverses
both types and values, including opaque values and constructor dependencies.
Every axiom list is required to be a subset of the standard triple.

```text
'Turing.loop_run' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.FinTM.exists_loopCfgTM' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.FinTM.exists_loopTM' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.FinTM.exists_loopFindTM' depends on axioms: [propext, Classical.choice, Quot.sound]
CLOSURE_AUDIT_PASS declarations=100; every checked declaration has empty admission roots and only standard axioms.
```

## Verification and environment

- Lean 4.25.0, release commit `cdd38ac5115bdeec5f609e9126cce00f51ae88b3`.
- Mathlib `029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e`; committed manifest unchanged.
- `lake exe cache get` was invoked once; the launcher failed before cache
  processing. Reused the available pinned dependency/cache tree after checking
  all 11 materialized package revisions against the manifest. Four packages
  for documentation generation were not materialized and are not needed by
  the required module sweep. No `lake build` was invoked.
- This runner's PID namespace/procfs mismatch blocked Lean's executable-path
  lookup. The small `verification/self-exe.c` compatibility shim redirects only
  its own `/proc/<pid>/exe` lookup to `/proc/self/exe`. The pinned Lean executable,
  libraries, proof checker, and kernel are unmodified. Setup details are recorded
  in `verification/environment.json`; reproduction instructions disclose the shim.
- Bootstrap: all 57 modules passed. Iteration used the owned module; final
  verification includes every subsequent module in the committed order.
- **Final full fresh sweep:** 57/57, 57 fresh nonempty oleans, zero `error:`
  lines, exit zero. The final output tree was new. A preceding complete sweep
  was repeated after the two trailing-space cleanups so the shipped bytes are
  exactly the verified source.
- Final declaration-admission warnings: **32**, all outside the owned file
  (4 pending primitives and 28 campaign admissions). Bootstrap had
  **33**. No out-of-scope admission was edited or used by a checked loop declaration.
- Lint: Build subtree 0 FAIL / 2 WARN over 4 files. Full TuringMachine subtree
  0 FAIL / 8 WARN over 28 files; ClassNP 0 FAIL / 1 WARN over 10 files.
  Combined, without counting the Build subset twice: 0 FAIL / 9 WARN over
  38 distinct files. These are file-size warnings; the owned file is addressed below.
- `git diff --check`, reverse patch application check, and `git bundle verify` pass.

Final sweep tail:

```text
MODULE 56/57 TCSlib/Complexity/CookLevin
MODULE 57/57 TCSlib/Complexity/ClassNP
SWEEP_PASS modules=57 elapsed_seconds=157.9
```

## Shared lemmas, escalations, and file size

Requested shared lemmas: **none**. Statement-level escalations: **none**.
The construction is complete; no remaining admitted private or continuation
work is being passed to another agent.

The owned file is **2,693 lines**, up from the recorded 1,466-line checkpoint.
The brief requires this construction to remain in the owned file and forbids
moving it elsewhere. The forty private helpers supply the previously missing
actual-host phase proofs and their assembly, so the inherited size exception
is retained and its final size is explicitly reported for the maintainer's
records. No authorization for a separate refactor is presumed.

## Complete new-private inventory

All names are in `Turing.FinTM`. Line numbers refer to the delivered source.
Every entry is admission-free.

| Declaration | Kind | Line |
| --- | --- | ---: |
| `loopFuelCfg` | def | 1075 |
| `loopFuel_run` | lemma | 1084 |
| `loopFuel_init` | lemma | 1097 |
| `loopFrame_payload` | lemma | 1114 |
| `loopFrame_counter` | lemma | 1124 |
| `loopHost_fuel_rewind` | lemma | 1136 |
| `loopCopyTape` | def | 1186 |
| `loopCopy_read` | lemma | 1190 |
| `loopCopy_erase` | lemma | 1195 |
| `loopCopy_initial` | lemma | 1208 |
| `loopCopy_final` | lemma | 1216 |
| `loopHost_fuel_copy` | lemma | 1230 |
| `loopHost_fuel_return` | lemma | 1281 |
| `loopHost_fuel_setup` | lemma | 1336 |
| `loopFuelCaptured` | def | 1367 |
| `loopReady` | def | 1374 |
| `loopFuelCaptured_frame` | lemma | 1386 |
| `loopHost_prepare` | lemma | 1445 |
| `loopBodyPadded` | def | 1485 |
| `loopCall` | def | 1495 |
| `loopBodySource_run` | lemma | 1505 |
| `loopHost_anchor_return` | lemma | 1520 |
| `loopReady_call` | lemma | 1561 |
| `loopHost_release` | lemma | 1600 |
| `loopHost_start` | lemma | 1631 |
| `loopHost_halt_return` | lemma | 1651 |
| `loopCall_frame` | lemma | 1678 |
| `loopCall_reframe` | lemma | 1705 |
| `loopHost_borrow_step` | lemma | 1737 |
| `loopHost_borrow_run` | lemma | 1775 |
| `loopHost_borrow_rewind` | lemma | 1808 |
| `loopHost_borrow` | lemma | 1858 |
| `loopFrame_flag` | lemma | 1880 |
| `loopFlag_clear` | lemma | 1889 |
| `loopHost_reject` | lemma | 1900 |
| `loopHost_payload_rewind` | lemma | 1972 |
| `loopHost_frame_replay` | lemma | 2025 |
| `loopHost_accept` | lemma | 2060 |
| `loopHost_round` | lemma | 2126 |
| `loopHost_bound` | def | 2189 |

## Delivery and integration

- Full source at the original repository-relative path.
- One-commit `git format-patch` series in `patches/`.
- `fill-lib-L2.bundle`, advertising only `fill/lib-L2` and requiring the recorded base.
- Final and bootstrap sweep logs, axiom/root log, lint, freeze, bundle and patch checks in `logs/`.
- Reproducible checks, the governing continuation brief, and machine-readable
  environment/results/freeze records in `verification/`.
- `SHA256SUMS` covers every other file in the archive.

Apply the patch with `git am -3` to a checkout descended from the required
campaign branch, preserving concurrent P2 changes. The bundle provides the
same single commit. Re-run the campaign integration checks as usual; this ZIP
is a completed fill, not a continuation checkpoint.

**Notation.** Code-font identifiers denote the Lean declarations or local
variables in the delivered source. `word.length` is the counter width;
`c.output.length` is the captured payload length; `t` is a source round's
positive duration. `firstHaltTime` and `rewindTime` in the time table describe
the witnesses named `u` and `v` in `loopHost_prepare`.
