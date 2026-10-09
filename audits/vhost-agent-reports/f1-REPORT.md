# vhost-f1 — completed proof fill

## Delivery and base

- Result: **11/11 target statements filled**, with no remaining admitted proof in either owned file.
- Repository: `https://github.com/Shilun-Allan-Li/tcslib`.
- Source branch: `complexity/arora-barak-ch3-4`.
- Recorded base: `44d25413044aed185a83ece08f7c29d0446d38ce`.
- The brief cites `756657d0b45f41f2a5e93f976f3189ce99080772`; the recorded base is its immediate successor, the commit issuing this fill brief. No rebase occurred.
- Working branch: `fill/vhost-f1`.
- Delivery commit: `50f846477261689db83c4f4e629c9dad93a7ca96`.
- No push or pull request; no `lake build`.

The archive has a flat layout. `Simulation.lean` is the full replacement for
`TCSlib/Complexity/TuringMachine/Simulation.lean`; `VirtualInput.lean` is the full
replacement for `TCSlib/Complexity/TuringMachine/Build/VirtualInput.lean`.
The format-patch series and incremental git bundle are against the recorded base.
`SHA256SUMS` covers every other archive member.

## Filled statements and binding proof routes

| Statement | Implemented route |
|---|---|
| `MultiTapeTM.step_eq_of_agreeOn` | Split halted/live control; use equality of the complete transition action on the guarded state. |
| `MultiTapeTM.runFrom_eq_of_agreeOn` | Induct on the horizon with the strict-prefix guard; cite the one-step transfer. |
| `vhostEmitTM_step` | Adapt the `bufferedSecondCfg_step` template to buffer plus bank, retaining the output prefix. Cite the existing buffer-read and virtual-movement lemmas; preserve the halting action's writes and emission. |
| `vhostEmitTM_runFrom` | Chain the step contract and valid arrival tags by induction, citing the iteration identities. |
| `vhostEmitTM_visitedByTapeHead_bank` | Project the all-time run identity and identify the two finite images. |
| `vhostEmitTM_visitedByTapeHead_buffer` | Project the buffer head and identify the finite image of source input positions minus one. |
| `vhostCfg_buffer_head_mem` | Project the run identity and use the source input position's `Fin` bounds. |
| `vhostEmitTM_spaceUsed_le` | Split off the buffer tape; identify the bank sum exactly with source space and bound buffer visits by the prescribed interval. |
| `vhostEmitTM_emitting_halt` | Cite the step contract, substitute the halting/emitting action, and associate output concatenation. |
| `vhostSilentTM_runFrom` | Compose `embedSilentTM_runFrom` with `vhostEmitTM_runFrom`; no additional simulation induction. |
| `vhostSilentTM_spaceUsed_le` | Cite selected-tape equality and the capture-growth bound from `Embed`; sum the selected bank and sole capture tape, then apply the forwarding space bound. |

The forwarding step proof consumes `bufferTape_inputSymbol` and
`virtualMove_correct` at `c.mapState (fun _ => ())`: these existing lemmas use
`S : Type`, whereas the frozen target allows `S : Type*`. Mapping only the control
to `Unit` leaves the input position and input read definitionally unchanged. No
signature restriction or duplicate input lemma was introduced.

The imported surface does not expose `Fin.sum_univ_succ`/`Fin.sum_univ_add`.
The forwarding sum uses `Fin.addCases`, `Finset.sum_bij`, and
`Finset.sum_erase_add` to implement the same buffer/bank split without changing
imports. The silent sum uses the analogous selected/capture partition. All
space coefficients and horizons are unchanged.

## Declaration inventory and freeze

Exactly one new declaration, private in `VirtualInput.lean`:

- `Turing.vhostSilent_layout`: for every silent-host tape index, membership in
  the `Fin.castAddEmb 1` range is equivalent to value below `1 + m`, and
  nonmembership is equivalent to equality with `vhostCap m`. Both silent proofs
  use it to discharge capture disjointness; the space proof also uses its
  completeness to exclude any unaccounted ambient tape. It includes `m = 0`.

`Simulation.lean` adds no declarations. No declarations were removed.
Optional exports: **none**.
Requested shared lemmas: **none**; the sole helper is specific to this layout.
Docstring appendices to existing declarations: **none**. The new helper has its
own statement and proof sketch.

The byte-level freeze check replaces only the eleven filled bodies with their
original `sorry` bodies and removes the one new private helper; the resulting
files are byte-identical to the base. Thus all existing statements, definitions,
imports, options, attributes, docstrings, and non-target proofs are unchanged.
`freeze.log` records the checks. The patch application was checked against the
base using a temporary git index and reproduced the exact delivery commit tree;
the bundle also verifies (`packaging.log`). The diff touches only the two owned files;
`Build/Loop.lean`, `CookLevin/Hardness.lean`, and all other files are untouched.

## Duplication ledger

**new copies: none**.

The new host proofs adapt the binding buffered-host template and cite its shared
read/movement facts and the existing run algebra. Neither silent contract
reimplements the embedding simulation. No existing proved declaration was copied
into a new private declaration.

## Verification

- Lean: **4.25.0**, release commit `cdd38ac5115bdeec5f609e9126cce00f51ae88b3`.
- Mathlib: `029db123ddaa7f8fd0d18cea3b1b33bf84dacd1e`, matching the manifest.
- `lake exe cache get` completed successfully. The pinned local toolchain and
  dependency files were initially copied into this task's own directory from an
  existing local setup. A process-local executable-path compatibility shim was
  needed in this runtime; it does not change Lean or any proof source.
- The prescribed 65-module bootstrap was run in order, with supplemental checks
  for the current facade imports and the Build infrastructure. During initial
  cache extraction, three concurrent checks exited with a bus error; affected
  checks were retried after cache setup completed. No source was changed to
  address these environment failures. An early facade check preceded the
  `UnaryTape` bootstrap; it was rerun after bootstrap completion. That failed
  attempt is preserved separately in `verification-retries.log`;
  `final-sweep.log` contains the five successful fresh checks in order.
  Out-of-scope baseline admissions were left untouched.
- Final checks use `scripts/lean_check_tree.sh`, which removes the old target
  `.olean` before elaboration and requires a fresh one. All five final modules
  pass with zero errors and zero sorry warnings, in the required order.

Final sweep summary (full diagnostics in `final-sweep.log`):

```text
PASS TCSlib/Complexity/TuringMachine/Simulation: errors=0; sorry_warnings=0; fresh_olean=yes
PASS TCSlib/Complexity/TuringMachine/Build/Embed: errors=0; sorry_warnings=0; fresh_olean=yes
PASS TCSlib/Complexity/TuringMachine/Build/VirtualInput: errors=0; sorry_warnings=0; fresh_olean=yes
PASS TCSlib/Complexity/TuringMachine/Build/Catalog: errors=0; sorry_warnings=0; fresh_olean=yes
PASS TCSlib/Complexity/TuringMachine: errors=0; sorry_warnings=0; fresh_olean=yes
FINAL: 5/5 PASS; 0 errors; 0 sorry warnings; all five oleans freshly produced.
```

All eleven axiom prints, from the final fresh tree (`axioms.log`):

```text
'Turing.MultiTapeTM.step_eq_of_agreeOn' depends on axioms: [propext, Quot.sound]
'Turing.MultiTapeTM.runFrom_eq_of_agreeOn' depends on axioms: [propext, Quot.sound]
'Turing.vhostEmitTM_step' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.vhostEmitTM_runFrom' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.vhostEmitTM_visitedByTapeHead_bank' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.vhostEmitTM_visitedByTapeHead_buffer' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.vhostCfg_buffer_head_mem' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.vhostEmitTM_spaceUsed_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.vhostEmitTM_emitting_halt' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.vhostSilentTM_runFrom' depends on axioms: [propext, Classical.choice, Quot.sound]
'Turing.vhostSilentTM_spaceUsed_le' depends on axioms: [propext, Classical.choice, Quot.sound]
```

Every footprint is a subset of `[propext, Classical.choice, Quot.sound]`; none
contains `sorryAx` or any additional axiom.

Style lint, one directory per invocation:

- `TCSlib/Complexity/TuringMachine/Build`: **0 FAIL**, 3 inherited file-size WARNs.
- `TCSlib/Complexity/TuringMachine`: **0 FAIL**, 10 file-size WARNs.

`Simulation.lean` is now 1,014 lines. Its existing size deviation is justified in
`AroraBarakChapters3-4Plan.md`, decision-log row **A-S1 spec layer LANDED**:
decision 13.5 locates Z5 beside the lockstep infrastructure, and a split belongs
to the queued D7 window. This fill adds nine lines net to that file and does not
split it. `VirtualInput.lean` is 506 lines. Full lint output is included in
`style-build.log` and `style-machine.log`.

## Completion checklist

- [x] 11/11 frozen target statements filled.
- [x] Base commit and the sole new private declaration recorded.
- [x] Optional exports and requested shared lemmas recorded as none.
- [x] Duplication ledger: new copies none.
- [x] Five final checks: zero errors, zero sorry warnings, fresh oleans.
- [x] Eleven axiom prints: only the permitted standard axioms, no `sorryAx`.
- [x] Both style checks: zero FAIL.
- [x] Diff restricted to the two owned files.
- [x] Full sources, patch series, git bundle, logs, and checksums included.

No remaining proof frontier or escalation.
