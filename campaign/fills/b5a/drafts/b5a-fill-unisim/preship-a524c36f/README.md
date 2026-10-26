# B5a, the uniform simulator: the pre-ship re-run at `a524c36f` (the tree after #162; maintainer, 2026-10-25)

Tree: the campaign tip `a524c36f` (a records commit), whose Lean content equals #162's merge
`5a258cc2` and its replayed head `d4759581`; the olean snapshot is `oleans-lkit2`, that replay's.
The drafting pre-ship is `../preship-77f1eb4f/` (TCSlib as after #155). Since then, three Lean
changes have landed in or around this item: #156 and #159 edited the owned file's
`canonEmitVerdict` (net −2 lines); #160 proved `NDCodeSimulator`'s replay canonizer; #162
published the startup kit `Build/InterpreterStartup` (the ruling Q-B1 = A) and re-pointed
`NDCodeSimulator` to it. Lean ran through `tools/leanelab.sh` against `oleans-lkit2`, at most two
elaborations at a time. Each `.out` is the raw output with paths stripped, and its last line gives
the time and the peak memory. **The overlay** (`CodeSimulatorOverlay.lean.txt`) is the owned file
with the brief's six imports after line 15, the kit sixth.

| Check | Result | File |
|---|---|---|
| Owned file, base | `CodeSimulator` (8,666 lines; 12 public, 185 private; the stub's docstring 8552–8653, statement 8654, `sorry` 8662; blob `733a9a46`): exactly the stub's sorry warning (8654); 19 s, 2.49 GB | `elab-CodeSimulator-base.out` |
| Owned file, overlay | exactly the stub's sorry warning (8660); 19 s, 2.50 GB | `elab-CodeSimulator-overlay.out`, `CodeSimulatorOverlay.lean.txt` |
| Imports | no cycle (none of the six imports' closures contains `CodeSimulator`); the six with every module downstream of `CodeSimulator` import together with no clash | `ImportClashProbe.*` |
| Order list | 120 modules: the drafting list's 119 and `Build/InterpreterStartup`, in the overlay's topological order (the kit before `CodeSimulator`); 41 Mathlib roots, the same | `order.txt`, `roots.txt` |
| Base sorries | 30 declarations in 14 modules: the drafting set less `NDCodeSimulator`'s `exists_replayCanonizer` (#160) | `base-sorries.txt` |
| Import probe | a standalone import of the owned module and the six: **157 checks of 157 names**, 0 errors, 0 warnings. The names: the drafting probe's 109, the review's 28 more (`B5aUSImportProbeExt`), the kit's eight, the phase host's four (#156, #159), and the H1 loop's step reader, virtual host and clock (8). 26 axiom prints, all within the standard three | `B5aUSImportProbe.*` |
| Route probe | the review's copy plus the kit import, sealed over 12 TCSlib definitions (the two `@[simp]` `initCfg`s erased): `b5a_install`, `b5a_locality`, `b5a_accepts_take`, `b5a_verdict`, `b5a_table_le`. 0 diagnostics; the standard three | `B5aUSRouteProbe.*` |
| Start probe | the review's probe re-pointed: the local copy of the capture-initial identity removed, the kit's `Turing.embedSilentCfg_initCfg` cited. `S`'s initial configuration through `initCfg_with_q₀`, `runFrom_with_q₀` and a five-line `Cfg.init` relabelling, sealed over 9: 0 diagnostics. Its 9 controls (new at issue; eight are the kit gate's goals, the input rewind's is new): all close unsealed and fail sealed, each at its own goal | `StartProbe.*`, `StartSealControl.*` |
| Home probes | the overlay with the review's `us_` block at the home (before `end StepBlockClients`, overlay line 8556): unsealed, only the target's sorry (8748); sealed over 18, only the target's sorry (8758); the standard three. Each probe differs from the overlay by exactly the review's inserted lines (checked) | `HomeProbe.*`, `HomeProbeSealed.*` |
| Verdict probe | the overlay with the 48-line block (`B5aUSVerdictProbe.append.lean.txt`) before `end MachineFormat`: only the target's sorry (8660); `b5a_window_verdict` on the standard three | `B5aUSVerdictProbe.*` |
| Seal controls | **18 goals**, one per definition sealed by the route, verdict and home probes: the drafting 16 and, at issue, `pairEncode` and `unaryFin` (the home probe's two more, the kit gate's goals). Unsealed, all close; sealed, all 18 fail, each at its own goal (lines 107–177) | `B5aUSSealControl.*` |
| Screen base | the 57-file population on a frozen worktree at the tip (`wt-mc`, `a524c36f`, no tracked change): **2,800 declarations, 3,026 pairs, 977,536 characters**; 53 minutes under `nice -n 10`, **peak resident memory 7.8 GB** (`/usr/bin/time -l`, the largest child's maximum resident set; the drafting record gives "about 100 MB resident", by a method it does not record). The owned file's pairs are the drafting base's: 99, 58 within (4 at 90% or more, CC7-1's) and 41 across (one at 90% or more, `canonOffset_spec` of `Encoding`'s `length_bits_le_self`, 65 of 65 characters). Against the drafting base: 22 new pairs and 1 gone, none with the owned file on either side. They come from the three files added to the population (SK-1's pair `embedSilentCfg_initCfg` ⇄ `ss_captureInitial`, 100% each way, ledgered; `Configuration`'s and `StateRenaming`'s existing pairs, newly screened) and from code changed since drafting (#156's `phaseHostTM_run`, #160's `rc_` canonizer privates) | `screen-base.*`, `screen-population.txt`, `pairdiff-vs-drafting-base.txt` |
| Lint | `TuringMachine`: 0 FAIL, 67 WARN over 84 files; `CodeSimulator`'s are its size and check 8 (`MachineFormat.toFinTM`, `codeSkipTableK`, `oneTapeMachineFormat`). `Diagonalization`: 0 FAIL, 2 WARN over 5 files | `lint-turingmachine.txt`, `lint-diagonalization.txt` |

**The screen population** is the brief's 57 files: the drafting 54, plus the two model files
whose lemmas the route reads (`Configuration`, `StateRenaming`, the review's F5), plus the kit's
module. None of the open PRs (#164 A1, #165 G4, #166 SCP) touches a file of it, so the screen base
stands whichever of them merges before issue.

**At issue.** If #164 or #165 merges first, re-run the lists. #165 removes `ZoneRebalance`'s two
sorries from the order list's base set; #164 adds `ClassP/TimeConstructible`'s
`timeConstructible_iff`, upstream of the owned file. Under #164, also re-run the overlay and the
probes (minutes). The owned file's lines do not move, since neither PR touches it. Stage them as
the draft's issue note says.
