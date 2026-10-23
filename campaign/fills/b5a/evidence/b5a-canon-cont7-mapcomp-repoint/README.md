# The canonizer's relabeling collapse re-pointed to `Cfg.mapState_mapState` (prepared, local)

#152's private `canonGramMapComp` (`TuringMachine/CodeSimulator.lean`) has the statement of #153's
public `Turing.Cfg.mapState_mapState`, with the composite written `fun s => g (f s)`. The v3 screen
matches the two at 99% each way. The prepared commit `e4c5d015` is on the local branch
`local/canon-mapcomp-repoint`: #152's head `8e74681a`, with #153 (`ac5ce7bc`) merged in locally as
`1588a7f7` so that the API is available, then the re-point. It removes the private and rewrites its
two sites with `Cfg.mapState_mapState`, each followed by `rfl`. The `rfl` closes the composite
`(g ∘ f)` against the old lambda through core's `Function.comp`; no repository definition is
unfolded. It applies at #152's landing only if the user so rules and #153 has merged.

- `repoint.py`: the asserted edit.
- `CCat.lean.txt`, `elab-CCat.out`: #153's module text followed by the re-pointed file, with the
  imports merged, against `oleans-lu2sc1`. The only warning is `exists_uniformSimulator`'s sorry.
- The canonizer review's own seal (`reviews/canon-cont7/scripts/mkseal.py`, its 36 names), at the
  re-pointed file's anchors (home 4939, the stub's end 8128):
  - `C7SealBodyCat`: 0 errors;
  - `C7SealCtlCat`: 74 errors, one on each control line;
  - `C7UnsealedCtlCat`: 0 errors, with 64 "rfl closes" and 10 clean examples.

  This is the review's result exactly.
- `freeze.txt`: 12 → 12 public; 186 → 185 private (`canonGramMapComp` removed); only
  `exists_canonGrammarStage` changed.
- `lint-tm.txt`: 0 FAIL. The one line over 100 characters predates this change; it is at the base.
- The screen (`CodeSimulator` and `Build/InputRewind`, at the local merge and after the
  re-point): 172 → 171 declarations, 78 → 67 pairs. 11 pairs are gone, including
  `canonGramMapComp` ↔ `Cfg.mapState_mapState` at 99%/99%, and none is new.
