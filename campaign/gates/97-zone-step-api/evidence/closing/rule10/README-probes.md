> **Run (2026-11-05, the cloud maintainer session).** Drafted by a sub-agent as text and then
> elaborated here, against `oleans-chk197`: a copy of the first cloud snapshot `oleans-cloud0`
> with #197's chain compiled into it (`../chain/`; the README below names the Mac's
> `oleans-lzsa`). The closing commit was amended once, to `20e7fc75` (minor 2's `simp only` names
> `nsmul_eq_mul` and `Nat.cast_id`), which changes `ZoneStep` only; `ZoneRebalance`'s blob is the
> one these probes were made from, and `ZoneStepSealed.lean.txt` carries the same one-line change.
> Results (`runs.txt`, `*.out`): `ZoneRebalanceSealed` **0 diagnostics** (461 s), with
> `Contract.zero` sealed file-wide; `SealControl_ZR` 49 pass unsealed, 49 fail sealed;
> `ZoneStepSealed` 0 diagnostics; `../axioms/Ax.out`: all 31 new public constants, and the 27 sweep
> lines, on subsets of `[propext, Classical.choice, Quot.sound]`.

# Gate 97 (#197, head `16e92449`): rule-10 seal of `ZoneRebalance`, `Contract.zero`'s controls, axioms

Prepared as text, not elaborated (finding 1, note 13). The PR head is
`16e9244976c17111d5403c1cfcf2ce52b0f4c916`; its base is `origin/complexity/arora-barak-ch3-4`
(merge base `683e2adf`). Between `0a1b64d5` and `16e92449` only `Build/ZoneRebalance`,
`Build/ZoneStep` and the facade changed. `Contract/Basic` is blob `d7d40bdd` at both commits.

## Files

| File | Purpose | Import line(s) | Oleans needed | Expected |
|---|---|---|---|---|
| `ZoneRebalanceSealed.lean.txt` | The whole of `Build/ZoneRebalance` at `16e92449`, sealed (see *The seal*). Re-verifies finding 1. | the module's own five: `Build.ZoneTape`, `Build.Contract.Basic`, `Build.Contract.Catalog`, `Build.Contract.Seam`, `CfgFacts` | #197's tree up to those five. `oleans-lzsa`, the `replay-lzsa` snapshot, serves, because none of them changed after `0a1b64d5`. Plain `leanelab.sh`, no overlay. | **0 diagnostics.** About 3 min: the module alone took 185 s in the chain. |
| `SealControl_ZR_unsealed.lean.txt` | The controls, with no seal | the same five | the same | **49 × `CONTROL_PASS`** |
| `SealControl_ZR_sealed.lean.txt` | The same controls, under the per-stretch seal and erasure | the same five | the same | **49 × `CONTROL_FAIL`** |
| `Ax.lean.txt` | `#print axioms` for all 31 new public constants of #197, plus a prefix sweep that cross-checks the `simps` names | `TCSlib.Complexity.TuringMachine.Build.ZoneStep` | #197's `ZoneRebalance` and `ZoneStep` at `16e92449`. Compile them with `leanelab-o.sh`, in that order, into a copy-on-write clone of `oleans-lzsa`, and elaborate against that overlay. | 31 `depends on axioms` lines, each a subset of `[propext, Classical.choice, Quot.sound]`, and no `sorryAx`. 27 `SWEEP` lines: the 23 new names that carry the prefixes, and the base's `zoneRebalancePost_state_done`, `zoneRebalancePost_frames`, `zoneExtendPost_frames` and `zoneRebalanceData_of_short`. An `unknown constant` error means a `simps` name is wrong; the sweep then shows the real one. |
| `zonestep-head/ZoneStepSealed.lean.txt` | An extra, not asked for. The gate's own `mkseal_zsa.py` re-run on `ZoneStep` at `16e92449`. The evidence copy is of `0a1b64d5`'s blob, which still has the private `zs_rowPre_mapState`. | `Build.ZoneRebalance`, Mathlib `BigOperators.Ring.Finset`, `Order.Ring.GeomSum` | the same overlay as `Ax` (#197's `ZoneRebalance`) | **0 diagnostics.** Regenerating gives byte-identical `SealControl_*` files, so the evidence's 36/36 and 0/36 still apply. |
| `mkseal_zr.py` | Writes the first three files and `seal-set-zr.txt`. Usage: `python3 -I mkseal_zr.py <ZoneRebalance.lean at 16e92449> <evidence/rule10/ctl_header.lean.part.txt> <out dir>`, with the input from `git -C /home/user/tcslib show 16e92449:TCSlib/Complexity/TuringMachine/Build/ZoneRebalance.lean`. | | | |
| `seal-set-zr.txt` | The 22 sealed definitions | | | |
| `tcsdefs.py`, `index-16e92449-zr.txt` | A textual index of the constants declared in `ZoneRebalance`'s import closure: 23 modules, 2464 constants, with kind, reducibility, instance and `@[simp]` flags. The same tool reproduces gate 95's Lean-generated 257-name candidate list exactly (see `../gate95/README.md`). | | | |
| `reach.py`, `reach-zr.txt` | For each changed stretch, the other-file definitions it names, directly or through an equation lemma (`<def>_<field>`). This is where the seal list comes from. | | | |

To elaborate a file, copy it to a `.lean` name in a worktree of #197, for example
`$TCSLIB_SCRATCH/wt-197/rvprobe/ZoneRebalanceSealed.lean`. The worktree needs its Mathlib link. Then
run `devtools/seyoon/leanelab.sh <wt> <olean dir> rvprobe/<file>.lean`.

## The seal (why the whole file, and where the seal sits)

**The whole file.** A restricted copy cannot work. Every proof this PR changed is `private`, and
those proofs rest on about 8k lines of the file's own private definitions
(`zr_reindexContract`, `zr_PinStep`, `zr_pinRe_step`, the host and scan contracts), which another
module cannot name. So the copy is all 15,402 lines, with two layers of seal added and nothing
else changed. Apart from the title line, `diff` against the blob shows only added lines.

1. **File-wide**, right after `namespace Turing`: `attribute [local irreducible] Turing.Contract.zero`.
   `Contract.zero` is the one other-file definition this PR makes newly reachable from the file's
   unchanged text, through the re-pointed `zr_anchorContract`. Finding 1 was exactly that case: at
   `0a1b64d5`, `zr_pinAnchor_step` had unchanged text but reduced `Contract.zero`. Every reader of
   `zr_anchorContract` lies below this seal, whether its text changed or not:
   - `zr_hostDispatchContract` and `zr_host_dispatch_run`;
   - the scan's branch contracts, `zr_scanBody_fields` and `_bounds`, and `zr_scan_round`;
   - `zr_pinAnchorContract`, `zr_pinAnchor_step`, `zr_anchBranch` and `_step`.
2. **Per changed stretch.** Each stretch the diff `683e2adf..16e92449` changed is wrapped in its own
   `section RV_<tag>`, which carries `attribute [-simp] Turing.Action.apply Turing.Cfg.init
   Turing.MultiTapeTM.initCfg` (the closure's `@[simp]` definitions) and `[local irreducible]` on the
   other 21 definitions of `seal-set-zr.txt`. The seven stretches:
   - `Equations`: the new `simps` attribute and `zoneRowPre_iff`, `_congr`, `_mapState_iff`,
     `zoneRebalanceIndex_eq`, `_le`;
   - `AnchorContract`;
   - `DispatchRun` (`zr_host_dispatch_run`);
   - `ScanBranches` (`zr_slotBranchContract`, `zr_blankBranchContract`);
   - `ScanBodyFields`;
   - `ScanBodyBounds`;
   - `PinAnchor` (`zr_pinAnchorContract`, `zr_pinAnchor_step`).

   The rest of the file's pre-existing proofs are not sealed beyond layer 1. They are not this PR's,
   and a file-wide seal of the whole list would test them as well.

`Contract.zero` is not repeated inside the sections. Lean refuses `[local irreducible]` on a
definition that is already irreducible (`ReducibilityAttrs.lean`: "`[semireducible]` expected"),
so repeating it would be an error. All 22 names are semireducible `def`s in the index. The reducible
`abbrev` `Turing.ZoneSym` cannot be sealed and may be read through its body (TEMPLATE).

**The seal list** (`seal-set-zr.txt`, 22 definitions) is `reach-zr.txt`, checked by hand:
- **From `reach-zr.txt`:**
  - `Contract.zero`, `.ofSegment`, `.seq`, `.branch`, `.inPhase`;
  - `Cfg.mapState`, `Cfg.workTapeSymbols`, `MultiTapeTM.runFrom`;
  - `skipTM_contract`, `seekPost`;
  - `zonedTape`, `zoneShiftIndex`.
- **Added by hand**, because they appear in the statements of the lemmas these stretches use, or
  in the types of their contracts:
  - `Cfg.bindState` (in `inPhase_post` and `zr_bindState_eq`);
  - `phaseHostTM` (under the abbrev `zr_hostTM`);
  - `Segment` and `HeadBox` (in `ofSegment`'s segment field);
  - `seamCompTM` and `seamCompTM₂` (the machines of `seq` and `branch`);
  - `skipTM`;
  - `FinTM.bufferTape` (in `zr_wordAt`);
  - `zoneRebalance` and `ZoneContents.extend` (in the `simps` equations' right sides).
- **Dropped:** `Contract.mapState`, a field-notation false positive (`.mapState` here is
  `Cfg.mapState`), and `ZoneSym`, which is reducible.

**`zr_pinAnchor_step` at the head, by inspection.**
- `zr_pinRe_step (zr_anchorContract x) (fun _ => ()) V T p _ h` gets its conclusion's contract
  `zr_reindexContract (zr_anchorContract x) …` by unfolding only the file's own
  `zr_pinAnchorContract`.
- The side goal is read through `rw [zr_anchorContract, Contract.zero_post, zero_time, zero_lo,
  zero_hi]`.
- The closing `⟨hd, rfl, rfl, rfl, …⟩` then needs only `d.inputPos = d.inputPos`,
  `d.output = d.output`, `0 = (fun _ => 0) j` (beta) and the file's own `zr_pinned`.
- So it should close with `Contract.zero` sealed.

The other changed proofs pass only lemma statements to `rw` and `simp only`. Their closing `rfl`s
reduce only core definitions (`Option.map`, `Option.bind`) and the file's own `zr_hostRed`.
`simps` needs only the file's own definitions to unfold, and the kernel ignores `irreducible`.

## The controls (`SealControl_ZR_*`)

The gate's control style is kept: its `ctl_header.lean.part.txt` is used verbatim (`#ctl_rfl` is
`c = <value>` by `rfl`; `#ctl_eqn` is the first equation lemma by `intros; rfl`). One new command is
added. `#ctl_stmt <lemma>` re-proves a published equation's statement by reduction, with
`intros; first | rfl | exact Iff.rfl`. Totals: 22 `rfl`, 22 `eqn`, and 5 `stmt`
(`Contract.zero_pre`, `_time`, `_post`, `_lo`, `_hi`), 49 in all. For `Contract.zero` these are:
- **the `rfl` delta goal:** `#ctl_rfl Turing.Contract.zero`, i.e. `Contract.zero = fun M e ι x => Contract.ofSegment …`;
- **the equation goals:** `#ctl_eqn Turing.Contract.zero` (`Contract.zero.eq_1`), and the five
  `#ctl_stmt` lines, e.g. `(Contract.zero M e ι x).post i d = d` by `rfl`.

None of the 22 definitions is recursive (`runFrom` is `tm.step^[t] cfg`), so every control
should pass unsealed. Sealed, every `rfl` needs a sealed constant to unfold, so none should pass.
The sealed file seals all 22 once, inside `section Controls`.

## Axioms (`Ax.lean.txt`): the 31 new public constants of #197

- `Contract/Basic` (6): `Contract.zero` and `zero_pre`, `_time`, `_post`, `_lo`, `_hi`.
- `ZoneRebalance`, from `simps` (14):
  - `ZoneData k` is the reducible `Σ ℓ, Fin k → ZoneContents ℓ`, so the data maps get `fst` and
    `snd`: `zoneRebalanceData_fst`, `_snd`, `zoneExtendData_fst`, `_snd`;
  - the endpoints are `{ d with … }` over `Cfg`, whose fields are `state inputPos workTapes
    workTapePos output`. That gives `zoneRebalancePost_` and `zoneExtendPost_` followed by
    `state`, `inputPos`, `workTapes`, `workTapePos`, `output`.
- `ZoneRebalance`, declared (5): `zoneRowPre_iff`, `zoneRowPre_congr`, `zoneRowPre_mapState_iff`,
  `zoneRebalanceIndex_eq`, `zoneRebalanceIndex_le`.
- `ZoneStep`, a new module (6): `zoneTrackStepData`, `zoneTrackStepData_of_lt`, `_of_not_lt`,
  `exists_zoneTrackStepTM`, `sum_two_pow_le_of_count`, `sum_cost_le_of_count`.
- The facade adds only an import and a docstring line.

The names were worked out from the attribute lines and the structures' fields. The old probe's
`zoneRebalancePost_workTapePos`, `zoneExtendPost_output`, `zoneRebalanceData_fst` and
`zoneExtendData_snd` confirm the pattern. The `#ax_prefix` sweep at the end of the file checks it
in Lean.

## Unsure

- Nothing here was elaborated. "0 diagnostics" for the sealed copy is a reading of the seven
  stretches and of the anchor's readers, not a run.
- The seal list is textual. A walk over the elaborated terms, such as gate 95's `#rv_seal_audit`
  appended to the sealed copy, would be the authoritative "reached" set.
- If a sealed stretch fails, the failing definition and line show which proof reads another file's
  definition by reduction.
