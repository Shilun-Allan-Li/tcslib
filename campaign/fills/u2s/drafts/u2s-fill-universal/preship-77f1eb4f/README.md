# U2, the `k`-tape universal machine: the pre-ship at the campaign tip `77f1eb4f` (drafting agent, 2026-10-24)

Tree: `77f1eb4fb74deb7a1ac7bae7bc4e98d5d0f9a532` (the campaign tip when megafill C's drafting
started; TCSlib as after #155). Olean tree: the fresh bootstrap of the union of megafill C's three
new order lists (119 modules; `campaign/fills/megafill/drafts/megafill-C-env-77f1eb4f/logs/`).
Every probe ran through `scripts/lean_check_tree.sh` as a copy under the clone's ignored
`.lake/probes/`, one Lean process at a time; each `.out` holds the output, the time, the peak
memory and the exit status. **The overlay** (`UniversalKOverlay.lean.txt`) is the owned file with
the brief's one import, `Build/Rewind`, after line 11.

| Check | Result | File |
|---|---|---|
| Owned file, base | `UniversalK` (1,762 lines; 12 public, 39 private; U2-U's statement 1716, `sorry` 1725; U2-E's 1754, `sorry` 1760): exactly the two targets' sorry warnings. Its bootstrap check: 5 s, 2,132,612 KiB | `elab-UniversalK.out` |
| Owned file, overlay | exactly the two warnings (1717, 1755) | `elab-UniversalKOverlay.out`, `UniversalKOverlay.lean.txt` |
| Import | no cycle (`Build/Rewind`'s closure is `Build/Catalog`'s); `SelfUniversal` and the facade gain its names; `SelfUniversal` declares none of them | (this README) |
| Order list | 96 modules (the base list's set; computed on the overlay by `fillinputs-overlay.py`); 40 Mathlib roots | `order.txt`, `roots.txt`, `fillinputs-overlay.py` |
| Base sorries | 27 declarations in 12 modules | `base-sorries.txt` |
| Import probe | a standalone import of the owned module and `Build/Rewind`: **77 checks of 77 names**, 0 errors, 0 warnings; the startup, H2-F, H5, `Lockstep.runFrom` and `rewindTM_run_ofCfg` on the standard three | `U2UEImportProbe.*` |
| Route probe | **against the proposed API**: the field equations of `StepBlock.forwardLoopCfg` and `rulerHostCfg` stated as theorems proved by `rfl` before the seal (stand-ins: Lean refuses `simps` on another module's declaration), then, sealed over 8 TCSlib definitions (`MultiTapeTM.initCfg` and `Cfg.init` also erased from `simp`): `u2_encode_init_tapes`, `u2_encode_init_fields`, `u2_encode_halt`, `u2_ruler_fields`. 0 diagnostics | `U2UERouteProbe.*` |
| Seal controls | 8 goals: unsealed, all close; sealed, all 8 fail, each at its own goal. The first two (`forwardLoopCfg`, `rulerHostCfg`) are the API gap: their fields are read only by unfolding | `U2UESealControl.*` |
| Screen base | ⟨U2-SCREEN⟩ | `screen-base.*`, `screen-population.txt` |
| Lint | `TuringMachine`: 0 FAIL, 68 WARN over 83 files. **Check 8 lists `Build/StepBlockForward`'s `forwardLoopCfg` and `Build/InputDevice`'s `RulerAt`, `rulerHostCfg`**: public definitions with no lemma beside them | `lint-turingmachine.txt` |

**The API gap (the drafting report's Q-U1).** No published lemma reads `forwardLoopCfg`'s or
`rulerHostCfg`'s fields (searched: no `forwardLoopCfg_*`, `rulerHostCfg_*` or `simps` attribute in
the tree or on the open PR heads). The seam of each phase is an equality of configurations with one
of them, so rule 10 leaves no route: an API PR first, with the stand-ins' statements.

**The copy-hazard search.** No private writer of a header-length ruler (the "rulers" of
`ClassNP/ExhaustiveReplay` and of G4's walk are work-tape words), lockstep composition into H2-F, or
`forwardLoopCfg`/`rulerHostCfg` reader exists outside the defining modules' own privates (`fl_*`,
`rd_*`); `SpaceComplexity/Hierarchy`'s `space_universal` (sorried) is the other future consumer of a
header ruler; the chapter-1 universal machine's code-first startup (`UniversalInterpreter`) is the
older device. The open PR heads (#156, #135) add none.

**At issue**, after Q-U1's API PR merges, re-run this pre-ship at the issue commit, replacing the
stand-ins by the published names, and stage: the overlay, the probes and the population into
`campaign/fills/u2s/inputs/u2s-fill-universal/`, `order.txt` as
`campaign/fills/u2s/orders/u2s-fill-universal.txt`, `base-sorries.txt` and `screen-base.txt` as
`campaign/fills/u2s/logs/u2s-fill-universal-{base-sorries,screen-base}.txt`, and this table as the
pre-ship log.
