<!-- campaign/backlog.md, lines 874-889, verbatim -->

### RW-1: the rewind row's frame helper, a copy of Catalog's seek frame (user, 2026-10-18)

*Origin: the screen of PR #138 (the public rewind row, `Build/Rewind`), before gate 55.*

`Build/Rewind`'s private `rw_cfg` reproduces `Build/Catalog`'s private `catalogSeekCfg` at 100%
(79 characters, both ways): the three-line record update that sets the state and moves one head,
over `RewindPhase` instead of `SeekPhase`. Catalog's helper is private and specific to
`SeekPhase`, so the new module cannot cite it. The step lemmas over the two frames, `rw_step` and
Catalog's private `catalog_seek_step`, state the same step; the screen pairs them below its
half threshold.
- **Acknowledged (user, 2026-10-18)**, before gate 55, on condition that the retirement stays on
  this backlog.
- **Retirement, in the user's dedup window:** publish one frame over any state type (with its
  step lemma, through the public `step_of_tapeAction_move`) and cite it from both files. It
  edits `Build/Catalog`, whose downstream is most of the library, so it goes with Catalog's next
  edit (12.2c T3, Catalog core, or MIG-1).
