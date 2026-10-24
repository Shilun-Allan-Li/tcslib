# B5a, the uniform simulator: the pre-ship at the campaign tip `77f1eb4f` (drafting agent, 2026-10-24)

Tree: `77f1eb4fb74deb7a1ac7bae7bc4e98d5d0f9a532` (the campaign tip when megafill C's drafting
started; TCSlib as after #155). Olean tree: the fresh bootstrap of the union of megafill C's three
new order lists (119 modules; `campaign/fills/megafill/drafts/megafill-C-env-77f1eb4f/logs/`).
Every probe ran through `scripts/lean_check_tree.sh` as a copy under the clone's ignored
`.lake/probes/`, one Lean process at a time; each `.out` holds the output, the time, the peak
memory and the exit status. **The overlay** (`CodeSimulatorOverlay.lean.txt`) is the owned file
with the brief's five imports after line 15; the order list is computed on it.

| Check | Result | File |
|---|---|---|
| Owned file, base | `CodeSimulator` (8,668 lines; 12 public, 185 private; the stub's docstring 8554–8655, statement 8656, `sorry` 8664): exactly the stub's sorry warning (8656). Its bootstrap check: 51 s, 2,956,472 KiB | `elab-CodeSimulator.out` |
| Owned file, overlay | 8,673 lines: exactly the stub's sorry warning (8661); 54 s, 2,961,864 KiB | `elab-CodeSimulatorOverlay.out`, `CodeSimulatorOverlay.lean.txt` |
| Imports | no cycle: none of the five imports' closures contains `CodeSimulator`. Of the nine modules downstream of it in the order list, five gain names through the overlay (`Diagonalization/EXPCOM`, `Diagonalization/Relativization`, `Codes2Tape`, `UniversalK`, `SelfUniversal`); none declares a name the gained modules declare (a textual census) | (this README) |
| Order list | 119 modules, the base list's set, in the overlay's topological order (`Build/Rewind`, `BufferWords`, `Build/SeamLayout`, `Build/InputWindow` now before `CodeSimulator`); 41 Mathlib roots, the base's | `order.txt`, `roots.txt`, `fillinputs-overlay.py` |
| Base sorries | 31 declarations in 15 modules; the bootstrap's sorry warnings agree module by module | `base-sorries.txt` |
| Import probe | a standalone import of the owned module and the five: **109 checks of 109 names**, 0 errors, 0 warnings; `exists_polyCanonizer`, `exists_installCallTM`, `exists_seamLayoutTM`, `exists_inputWindowCopyTM`, `hostedLoopTM_run`, `rewindTM_run_ofCfg`, `runWith_initCfg_take` on the standard three, `inputRewindTM_run` on two | `B5aUSImportProbe.*` |
| Route probe | sealed over 12 TCSlib definitions (the `@[simp]` `MultiTapeTM.initCfg`, `NDTM.initCfg` also erased): `b5a_install`, `b5a_locality`, `b5a_accepts_take`, `b5a_verdict`, `b5a_table_le`. 0 diagnostics; all on the standard three | `B5aUSRouteProbe.*` |
| Verdict probe | in-module: the overlay with the 48-line block of `B5aUSVerdictProbe.append.lean.txt` before its final `end`s, sealed over 4 more definitions: `b5a_window_verdict` (the file's private `h1HostedVerdict_accepts` on the window `x.take t` decides acceptance on `x`). Only the stub's warning; the standard three. The assembled file's SHA-256 is in `B5aUSVerdictProbe.assembled.sha256` | `B5aUSVerdictProbe.*` |
| Seal controls | 16 goals, one per sealed definition: unsealed, all close; sealed, all 16 fail, each at its own goal | `B5aUSSealControl.*` |
| Screen base | the 54-file population: **2,756 declarations, 3,005 pairs, 973,130 characters**; 99 pairs have an owned-file declaration on one side: 58 within the file (4 at 90% or more: `canonGramCut_leg`/`canonStageCut_leg` both ways, `canonStageLeg4` and `canonStageLeg5` of `canonStageLeg1`, all CC7-1), 41 across files (one at 90% or more: `canonOffset_spec` reproduces `Encoding`'s `length_bits_le_self`, 65 of 65 characters; the rest at most 86%); 87 minutes under `nice -n 10`, about 100 MB resident | `screen-base.*`, `screen-population.txt` |
| Lint | `TuringMachine`: 0 FAIL, 68 WARN over 83 files; `CodeSimulator`'s are its size and check 8 (`MachineFormat.toFinTM`, `codeSkipTableK`, `oneTapeMachineFormat`) | `lint-turingmachine.txt` |

**The copy-hazard search.** The would-be copies of this route are already in the tree, privately:
`NDCodeSimulator`'s startup (`ic_header_result`, `ic_capture_return`, `ic_header_capture`,
`ic_input_suffix`, `ic_seam_step`, `ic_install_phase`, `ic_window_call`, `ic_layout_call`), UN's
(`un_canon_halt`, `un_step`, `un_step'`, `un_setup`) and U2-S's (`ss_capturedPrefix_run` and its
family). `ic_input_suffix` has the statement of the public `Complexity.Codec.pe_drop` and of
`Logspace/PathWalk`'s private `drop_pairEncode`. The population holds every file of these; the
open PR heads (#156, #135) add none. The drafting report's Q-B1 is the decision this raises.

**The lists' tool.** `fillinputs-overlay.py` is `devtools/seyoon/fillinputs.py` with one asserted
change: the module named by `OVERLAY_MODULE` is read from `OVERLAY_FILE` instead of the revision.

**At issue**, after the user's ruling Q-B1, re-run this pre-ship at the issue commit and stage:
the overlay, the probes and the population into `campaign/fills/b5a/inputs/b5a-fill-unisim/`,
`order.txt` as `campaign/fills/b5a/orders/b5a-fill-unisim.txt`, `base-sorries.txt` and
`screen-base.txt` as `campaign/fills/b5a/logs/b5a-fill-unisim-{base-sorries,screen-base}.txt`, and
this table as the pre-ship log.
