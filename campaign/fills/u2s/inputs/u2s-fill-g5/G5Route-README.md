# G5's route probe: the frame and the zero-tape case (pre-ship, 2026-11-06)

Drafted by a sub-agent of the cloud maintainer session and reviewed by the maintainer. All three
lemmas are proved; the brief's inputs take these files once #202 merges, re-run on the merged tree.

## The probe (`G5Route.lean.txt`)

Imports: `TwoTapes`'s three, plus `Build.ZoneStep` and `Build.Embed` (the brief's region (a)
adds `Build.ZoneStep`; `Build.Embed` comes with R1). `namespace Turing.FinTM`, three privates
with docstrings that cite only [HS66], [AB09, §1.7] and library names:

| Lemma | Route step | Proof |
|---|---|---|
| `tt_zero_tapes (M) (hk : M.k = 0)` | 1 | R1 on two tapes: `embedEmitTM σ M.tm` with `σ : Fin M.k ↪ Fin 2` from `Fin.castLEEmb`, restarted at `M.tm.q₀` (`initCfg_with_q₀`, `runFrom_with_q₀`); the initial configuration by `initCfg_eq`, `embedEmitCfg_eq` and the `Cfg.init_*` equations; the run by `embedEmitTM_runFrom`; both directions through `embedEmitCfg_state`/`_output`; `c = 1` |
| `tt_frame (M) (HS : FinTM (ZoneSym M.k)) (hHS : HS.k = 2) (c₁) (hfwd) (hconv)` | 0 | `alphabet_reduction_run (Function.Embedding.inl) HS`, `c := c₂ * c₁`; `hfwd` and `hconv` are the draft's step 0 word for word |
| `tt_route (hHS) (M)` | 0 | `by_cases M.k = 0` |

## Checks

| File | Against `oleans-ldwa3` (and `oleans-lsi2`, #202's merged tree) |
|---|---|
| `G5Route` | exit 0, no output |
| `G5RouteSealed`: 15 other-file definitions irreducible (`FinTM.ComputesInTime`, `MultiTapeTM.ComputesInTimeAndSpace`, `spaceUsed`, `spaceUsedByTape`, `visitedByTapeHead`, `runFrom`, `initCfg`, `step`, `Cfg.init`, `Action.apply`, `Cfg.inputSymbol`, `Cfg.workTapeSymbols`, `moveInputPos`, `embedEmitTM`, `embedEmitCfg`), `[-simp]` on `MultiTapeTM.initCfg`, `Cfg.init`, `Action.apply` | exit 0, no output |
| `G5RouteCtl_unsealed` / `_sealed`: `#ctl_rfl` and `#ctl_eqn` per sealed definition, `#ctl_simp` for the three simp ones | 33 PASS / 33 FAIL |
| `G5RouteAxioms` | the three lemmas on `[propext, Classical.choice, Quot.sound]` |
| `G5RouteExact`: each lemma posed to `exact?` | no library lemma closes any of them (expected exit 1) |

The maintainer re-ran the first four on both snapshots (`maintainer-rerun.txt`); the outputs on
`oleans-ldwa3` are byte-identical to the sub-agent's.

## Two facts for the brief

- **The `with q₀` restart is needed.** With `embedEmitTM` sealed, `exact?` finds no lemma giving
  its `q₀` or its `initCfg` (`G5RouteQ0`, expected exit 1). `UniversalK` uses the same idiom.
- **`ZoneSym` has no declared instances.** `ZoneSym k := Bool ⊕ ZoneCell k` and `ZoneCell k` are
  `abbrev`s, and `Fintype`/`DecidableEq` come from `Sum`'s instances through them. Lean refuses
  `[local irreducible]` on a reducible constant (`G5RouteZoneSymStrict`), and forcing it breaks the
  statements' instances and `Function.Embedding.inl`'s type (`G5RouteZoneSym`). So the two
  abbrevs stay out of every seal, by necessity, not as an exemption.

## Inspection

Every `rw`/`simp only` argument is a theorem. The one `show` (line 83), the ascriptions at 89–90
and the `rfl` at 74 reduce only the projections of the explicit `{ k := 2, State := M.State,
tm := N }`, which is not another file's definition; the sealed copy confirms it. No `unfold`,
`delta`, `dsimp`, `change`, `decide`, bare `simp`, `simpa` or `sorry`. `G5RouteWalk` lists the
other-module constants each proof uses.

## Duplication

No published statement of any of the three in the tree, by statement scan and by `exact?`. The
nearest are private: `SingleTape`'s `unusedTapeTM` family (which the brief forbids copying, and
which was not copied), and run-level padding in `SAT` and `Hardness`. **A promotion candidate**,
not acted on: a public R1 corollary, `M.k ≤ K → ∃ M', M'.k = K ∧ ∀ x o t, M.ComputesInTime x o t ↔
M'.ComputesInTime x o t`, would cover `tt_zero_tapes` and the private padding family.
