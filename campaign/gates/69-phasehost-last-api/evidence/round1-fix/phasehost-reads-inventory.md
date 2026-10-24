# Other files' definitional reads of `Turing.phaseHostTM` at the round-2 head (`0e5f210b`)

Two searches, both over every file that names `phaseHostTM` (16 besides `Build/Seam`;
`sweep/files.txt`):

- **The seal sweep** (`sweep/`): each file elaborated with
  `attribute [local irreducible] Turing.phaseHostTM` after its imports (`mksweep.py`; the copy's
  lines are the source's plus 3), against `oleans-lphl`. An error marks a proof that closes through
  the host's definition. Lean stops a declaration at its first error, so a declaration is listed
  once even if it reads the host twice. `Contract/Basic`'s error is not a read: the file names
  `phaseHostTM` only in its documentation and does not import `Build/Seam`.
- **Explicit unfoldings** (`../residue.txt`, part 1): `simp`/`rw`/`unfold` arguments naming
  `phaseHostTM`, which a seal does not block. The `change`/`show` lines listed there restate a
  same-file wrapper as its host application and are not reads of the host.

None of the reads below re-derives `Turing.phaseHostTM_run_le` or
`Turing.phaseHostTM_tr_of_red_none` as a prefix or a table agreement for a run (those seven sites
are re-pointed by `0e5f210b`). They read one field of the host or take one step:

| File · declaration | Source line | Read | Published equation that would replace it |
|---|---|---|---|
| `SpaceComplexity/Inclusions` · `b2b_setup_capture` (`hinit`) | 921 | the host's start state, by `rfl` | none yet: a start-state equation |
| `Build/NDHost` · `phaseHostND_fixChoice` | 107 | the whole host (start state and table), by `rfl` | none yet: start-state and redirect-branch equations, with `phaseHostTM_tr_of_red_none` |
| `Build/OracleSim` · `oracleHost_initial` | 1904 | the host's start state (its `initCfg`), by `change` | none yet: a start-state equation |
| `Build/StepBlock` · `seekTM_request` | 1264–1265 | the redirect branch's dispatch, by `rfl`; the skipper's start state, by `simp [… phaseHostTM]` | none yet: redirect-branch and start-state equations |
| `Build/StepBlock` · `seekTM_observe` | 1718, 1724 | the router's table at two live states, by `rfl` | `phaseHostTM_tr_of_red_none` (the goals also close `Action.mapState` by definition) |
| `Build/StepBlock` · `seekTM_stateStep` | 1453 | one seek step, by `simp [MultiTapeTM.step, …, phaseHostTM, …]` | `phaseHostTM_tr_of_red_none` or the redirect-branch equation, with the step's field equations |
| `Build/StepBlock` · `roundTM_lookup` | 2989 | the seek host's start state, inside a `simpa` | none yet: a start-state equation |
| `Build/StepBlock` · `roundTM_canonical` | 3029 | the redirect branch's dispatch, by `rfl` | none yet: a redirect-branch equation |
| `Build/StepBlockForward` · `fl_hosted_leaf` | 224 | the leaf's table at a live state, by `rfl` | `phaseHostTM_tr_of_red_none` |
| `Build/StepBlockForward` · `fl_return` | 231–232 | the redirect branch's dispatch, by `rfl` | none yet: a redirect-branch equation |
| `Build/WindowRun` · `wl_stop_fixed` | 533 | one step at a stop state, by `simp only [MultiTapeTM.step, …, phaseHostTM, …]` | `phaseHostTM_tr_of_red_none`, with the step's field equations |
| `CodeSimulator` · `canonEmitVerdict` | 4602 | the host's start state (its `initCfg`), by `change` | none yet: a start-state equation |

**Disposition (user, 2026-10-24): a follow-up API PR after #156.** It publishes, beside
`phaseHostTM` in `Build/Seam`, a start-state equation (`(phaseHostTM M q0 red).q₀ = q0`) and a
redirect-branch table equation (for `red i s = some q'`, the host's action at `⟨i, s⟩` is the
stationary, silent, write-free dispatch to `q'`), and re-points the reads above, with its own gate
and replay. It lands before megafill C is issued (it changes `CodeSimulator`).
