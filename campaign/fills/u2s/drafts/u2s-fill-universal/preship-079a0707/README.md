# U2, the `k`-tape universal machine: the pre-ship re-run at `079a0707` (maintainer, 2026-10-25)

Tree: the campaign tip `079a0707` (records commit), whose Lean content is the tree after #161
(`cfaaf75a`; the olean snapshot `oleans-lu2api`, its merged-tree replay). The drafting pre-ship is
`../preship-77f1eb4f/` (TCSlib as after #155). This re-run follows the draft's "at issue" note
and gate 73's note 9: the route probe now cites #161's published field equations instead of local
stand-ins. Lean ran through `tools/leanelab.sh` against `oleans-lu2api`, one elaboration at a
time; each `.out` is the raw output (paths stripped).

| Check | Result | File |
|---|---|---|
| Owned file, base | `UniversalK` unchanged since drafting (1,762 lines): exactly the two targets' sorry warnings, at 1716 and 1754 | `elab-UniversalK.out` |
| Owned file, overlay | the drafting overlay (one import, `Build/Rewind`): exactly the two warnings (1717, 1755) | `elab-UniversalKOverlay.out`, `UniversalKOverlay.lean.txt` |
| Order list | 96 modules, the same set as at drafting; 40 Mathlib roots, the same | `order.txt`, `roots.txt`, `fillinputs-overlay.py` (unchanged) |
| Base sorries | 26 declarations in 11 modules: the drafting set less `NDCodeSimulator`'s `exists_replayCanonizer` (proved by #160) | `base-sorries.txt` |
| Import probe | the drafting probe's 77 checks plus 16: #161's ten field equations, `MultiTapeTM.spaceUsedByTape_eq_card`, `pairEncode_drop`, and the phase host's `phaseHostTM_run_le`, `phaseHostTM_tr_of_red_none` (#156), `phaseHostTM_q₀`, `phaseHostTM_tr_of_red_some` (#159): **93 checks of 93 names**, 0 errors, 0 warnings | `U2UEImportProbe.*` |
| Route probe | **against the published API**: the drafting probe's four lemmas (`u2_encode_init_tapes`, `u2_encode_init_fields`, `u2_encode_halt`, `u2_ruler_fields`), the stand-ins removed and the published names cited (the pointwise tape equations through one `funext` each; `rulerHostCfg_inputPos` by `rw`), sealed over the same 8 TCSlib definitions: 0 errors, 0 warnings; the axioms within the standard three | `U2UERouteProbe.*` |
| Seal controls | unchanged: 8 goals, all close unsealed, all 8 fail sealed (lines 59–88, inside the sealed section 50–90) | `U2UESealControl.*` |
| Screen base | the drafting 20-file population at the tip (`39c649e6`): **1,065 declarations, 790 pairs, 214,291 characters**, about 6.5 minutes under `nice -n 10`. Against the drafting base, 5 new pairs and none gone, none with `UniversalK` on either side: #160's canonizer privates in `NDCodeSimulator` (three, at most 62%) and #161's `pairEncode_drop` ⇄ `NDCodeSimulator`'s `ic_input_suffix` (100%, the ledger's SD-1, which #162 removes). The owned file's pairs are the drafting base's: 13 within (none at 90% or more), one across (`ss_inputRewind_run` of `Universal`'s `timedFrame_run`, 56%) | `screen-base.*`, `pairdiff-vs-drafting-base.txt`, `screen-population.txt` |

**At issue** (megafill C, with B5a after #162): the open PRs touch this order list. #164 (A1)
changes `ClassP/TimeConstructible` and `SpaceComplexity/Basic`, both in it; #165 (G4) changes
`Build/ZoneRebalance` (now about 15,000 lines, about 3 minutes and 4.5 GiB to elaborate) and the
`TuringMachine` facade, both in it through the facade's closure; #162 changes the facade too. If
any of them is in the issue base, re-run the overlay, the probes and the order list there (the
owned file's lines will not move: none of them touches it); then stage them as the draft's "at
issue" note says.
