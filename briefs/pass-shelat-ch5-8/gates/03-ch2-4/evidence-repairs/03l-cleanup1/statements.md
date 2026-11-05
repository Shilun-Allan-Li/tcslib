# Statement diff: gate 03l clean-up, part 1 (and item H)

Base `0c348ff94cacf24d96d99078c9dd9e328530c8d2` → head `f29be161cd86cfc3a9c38bd203bfa095b4974086`. Every public declaration of the changed `.lean` files that was added, removed, renamed or has a changed statement (extracted by `g03l-fix/decls.py`, normalized statement text up to the depth-0 `:=`, then matched by hand for renames). Line numbers: base file:line → head file:line.

No public statement outside items A–D and H changed. `SAT.lean`, `PairSplit.lean`'s `exists_pairSplitTM`, `UnaryMul.lean`'s `exists_unaryMulTM`, `Closure.lean`'s `exists_comp` and every theorem of `Repetition.lean` keep their statements.

## Moved and renamed (item A: the clean-module host)

| Old (base file:line) | New (head file:line) | Statement |
|---|---|---|
| `Complexity.IterateFind.Clean` (TCSlib/Complexity/Randomized/Build/IterateFindHost.lean:186) | `Turing.ModuleHost.Clean` (TCSlib/Complexity/TuringMachine/Build/ModuleHost.lean:197) | definition identical (namespace moved) |
| `Complexity.IterateFind.clean_install` (TCSlib/Complexity/Randomized/Build/IterateFindHost.lean:235) | `Turing.ModuleHost.clean_install` (TCSlib/Complexity/TuringMachine/Build/ModuleHost.lean:269) | statement identical (namespace moved) |
| `Complexity.IterateFind.clean_emit` (TCSlib/Complexity/Randomized/Build/IterateFindHost.lean:255) | `Turing.ModuleHost.clean_emit` (TCSlib/Complexity/TuringMachine/Build/ModuleHost.lean:293) | statement identical (namespace moved) |
| `Complexity.IterateFind.HostState` (TCSlib/Complexity/Randomized/Build/IterateFindHost.lean:531) | `Turing.ModuleHost.State` (TCSlib/Complexity/TuringMachine/Build/ModuleHost.lean:385) | generalized: `HostState M = Fin 3 ⊕ Σ i, (M i).State` (`M : Fin 5 → FinTM Bool`) becomes `State C M = C ⊕ Σ i, (M i).State` (`M : Fin n → FinTM Bool`); IterateFind uses `State (Fin 3) M` |
| `Complexity.IterateFind.hostEntry` (TCSlib/Complexity/Randomized/Build/IterateFindHost.lean:534) | `Turing.ModuleHost.entry` (TCSlib/Complexity/TuringMachine/Build/ModuleHost.lean:394) | generalized in `n` and `C` (implicit); same body `.inr ⟨i, (M i).tm.q₀⟩` |
| `Complexity.IterateFind.host_call` (TCSlib/Complexity/Randomized/Build/IterateFindHost.lean:589) | `Turing.ModuleHost.host_call` (TCSlib/Complexity/TuringMachine/Build/ModuleHost.lean:462) | generalized: takes `{C} [Fintype C] [DecidableEq C] {n}`, `K`, `ctrl`, `ret`, `q₀` (the host `hostTM M K hk ctrl ret q₀` with `K` tapes, IterateFind passing `K + 1`); the guard says no control state is visited, `∀ v < t, ∀ c : C, state ≠ some (.inl c)` (was `≠ some (.inl 0)`); the endpoint is at `ret i` (was `hostRet M i`) |
| `Complexity.IterateFind.guard_add` (TCSlib/Complexity/Randomized/Build/IterateFindHost.lean:632) | `Turing.ModuleHost.guard_add` (TCSlib/Complexity/TuringMachine/Build/ModuleHost.lean:509) | statement identical (namespace moved) |
| `Complexity.IterateFind.host_clean` (TCSlib/Complexity/Randomized/Build/IterateFindHost.lean:646) | `Turing.ModuleHost.host_clean` (TCSlib/Complexity/TuringMachine/Build/ModuleHost.lean:530) | generalized as `host_call` (extra arguments `ctrl ret q₀`; guard `∀ c : C`; endpoint at `ret i`) |

IterateFind's `hostTM` stays (`IterateFindHost.lean`), now `abbrev hostTM M K hk := ModuleHost.hostTM M (K + 1) hk (hostCtrl M K) (hostRet M) (ModuleHost.entry M 0)`, with the same signature.

## Renamed (item C: `StateLoop.BlockLoop` → `StateLoop.BlockMapLoop`)

| Old (base file:line) | New (head file:line) | Statement |
|---|---|---|
| `Complexity.StateLoop.BlockLoop.start` (TCSlib/Complexity/Randomized/Build/StringLoops.lean:430) | `Complexity.StateLoop.BlockMapLoop.start` (TCSlib/Complexity/Randomized/Build/StringLoops.lean:521) | statement identical |
| `Complexity.StateLoop.BlockLoop.step` (TCSlib/Complexity/Randomized/Build/StringLoops.lean:436) | `Complexity.StateLoop.BlockMapLoop.step` (TCSlib/Complexity/Randomized/Build/StringLoops.lean:531) | statement identical |
| `Complexity.StateLoop.BlockLoop.acc` (TCSlib/Complexity/Randomized/Build/StringLoops.lean:441) | `Complexity.StateLoop.BlockMapLoop.acc` (TCSlib/Complexity/Randomized/Build/StringLoops.lean:545) | statement identical |
| `Complexity.StateLoop.BlockLoop.out` (TCSlib/Complexity/Randomized/Build/StringLoops.lean:445) | `Complexity.StateLoop.BlockMapLoop.out` (TCSlib/Complexity/Randomized/Build/StringLoops.lean:557) | statement identical |
| `Complexity.StateLoop.BlockLoop.rounds` (TCSlib/Complexity/Randomized/Build/StringLoops.lean:448) | `Complexity.StateLoop.BlockMapLoop.rounds` (TCSlib/Complexity/Randomized/Build/StringLoops.lean:564) | statement identical |
| `Complexity.StateLoop.BlockLoop.param_poly` (TCSlib/Complexity/Randomized/Build/StringLoops.lean:452) | `Complexity.StateLoop.BlockMapLoop.param_poly` (TCSlib/Complexity/Randomized/Build/StringLoops.lean:576) | statement identical |
| `Complexity.StateLoop.BlockLoop.rest_poly` (TCSlib/Complexity/Randomized/Build/StringLoops.lean:456) | `Complexity.StateLoop.BlockMapLoop.rest_poly` (TCSlib/Complexity/Randomized/Build/StringLoops.lean:581) | statement identical |
| `Complexity.StateLoop.BlockLoop.accum_poly` (TCSlib/Complexity/Randomized/Build/StringLoops.lean:460) | `Complexity.StateLoop.BlockMapLoop.accum_poly` (TCSlib/Complexity/Randomized/Build/StringLoops.lean:586) | statement identical |
| `Complexity.StateLoop.BlockLoop.start_poly` (TCSlib/Complexity/Randomized/Build/StringLoops.lean:464) | `Complexity.StateLoop.BlockMapLoop.start_poly` (TCSlib/Complexity/Randomized/Build/StringLoops.lean:590) | statement identical |
| `Complexity.StateLoop.BlockLoop.step_poly` (TCSlib/Complexity/Randomized/Build/StringLoops.lean:469) | `Complexity.StateLoop.BlockMapLoop.step_poly` (TCSlib/Complexity/Randomized/Build/StringLoops.lean:595) | statement identical |
| `Complexity.StateLoop.BlockLoop.acc_poly` (TCSlib/Complexity/Randomized/Build/StringLoops.lean:482) | `Complexity.StateLoop.BlockMapLoop.acc_poly` (TCSlib/Complexity/Randomized/Build/StringLoops.lean:608) | statement identical |
| `Complexity.StateLoop.BlockLoop.out_poly` (TCSlib/Complexity/Randomized/Build/StringLoops.lean:494) | `Complexity.StateLoop.BlockMapLoop.out_poly` (TCSlib/Complexity/Randomized/Build/StringLoops.lean:621) | statement identical |
| `Complexity.StateLoop.BlockLoop.orbit_eq` (TCSlib/Complexity/Randomized/Build/StringLoops.lean:498) | `Complexity.StateLoop.BlockMapLoop.orbit_eq` (TCSlib/Complexity/Randomized/Build/StringLoops.lean:625) | statement identical |
| `Complexity.StateLoop.BlockLoop.orbit_length_le` (TCSlib/Complexity/Randomized/Build/StringLoops.lean:521) | `Complexity.StateLoop.BlockMapLoop.orbit_length_le` (TCSlib/Complexity/Randomized/Build/StringLoops.lean:648) | statement identical |
| `Complexity.StateLoop.BlockLoop.acc_orbit_false` (TCSlib/Complexity/Randomized/Build/StringLoops.lean:546) | `Complexity.StateLoop.BlockMapLoop.acc_orbit_false` (TCSlib/Complexity/Randomized/Build/StringLoops.lean:673) | statement identical |
| `Complexity.StateLoop.BlockLoop.acc_orbit_true` (TCSlib/Complexity/Randomized/Build/StringLoops.lean:562) | `Complexity.StateLoop.BlockMapLoop.acc_orbit_true` (TCSlib/Complexity/Randomized/Build/StringLoops.lean:689) | statement identical |
| `Complexity.StateLoop.BlockLoop.out_orbit` (TCSlib/Complexity/Randomized/Build/StringLoops.lean:577) | `Complexity.StateLoop.BlockMapLoop.out_orbit` (TCSlib/Complexity/Randomized/Build/StringLoops.lean:704) | statement identical |

`Complexity.StateLoop.BlockLoop.blk` (TCSlib/Complexity/Randomized/Build/StringLoops.lean:433) is now private (`BlockMapLoop.blk`, review §3); `BlockMapLoop.step_eq` and `acc_eq` state its value `b.eval (pairFstD (pairFstD v)).length` explicitly.

## Changed statements

- `Complexity.IterateFind.hostRet` (TCSlib/Complexity/Randomized/Build/IterateFindHost.lean:539->283):
  - old: `def hostRet (M : Fin 5 → FinTM Bool) (i : Fin 5) : HostState M`
  - new: `def hostRet (M : Fin 5 → FinTM Bool) (i : Fin 5) : ModuleHost.State (Fin 3) M`
- `Complexity.IterateFind.hostTM` (TCSlib/Complexity/Randomized/Build/IterateFindHost.lean:547->312):
  - old: `def hostTM (M : Fin 5 → FinTM Bool) (K : ℕ) (hk : ∀ i, (M i).k ≤ K + 1) : FinTM Bool`
  - new: `abbrev hostTM (M : Fin 5 → FinTM Bool) (K : ℕ) (hk : ∀ i, (M i).k ≤ K + 1) : FinTM Bool`
- `Complexity.IterateFind.host_branch` (TCSlib/Complexity/Randomized/Build/IterateFindHost.lean:671->336):
  - old: `lemma host_branch (M : Fin 5 → FinTM Bool) (K : ℕ) (hk : ∀ i, (M i).k ≤ K + 1) (x : List Bool) (b : Bool) (w : List Bool) (hw : w[0]? = some b) : (hostTM M K hk).tm.step (Cfg.ofWords (input := x) (.inl 1) (stateWord (K + 1) w)) = Cfg.ofWords (hostEntry M (if b then 4 else 3)) (stateWord (K + 1) w)`
  - new: `theorem host_branch (M : Fin 5 → FinTM Bool) (K : ℕ) (hk : ∀ i, (M i).k ≤ K + 1) (x : List Bool) (b : Bool) (w : List Bool) (hw : w[0]? = some b) : (hostTM M K hk).tm.step (Cfg.ofWords (input := x) (.inl 1) (stateWord (K + 1) w)) = Cfg.ofWords (ModuleHost.entry M (if b then 4 else 3)) (stateWord (K + 1) w)`
- `Complexity.IterateFind.host_dispatch` (TCSlib/Complexity/Randomized/Build/IterateFindHost.lean:661->324):
  - old: `lemma host_dispatch (M : Fin 5 → FinTM Bool) (K : ℕ) (hk : ∀ i, (M i).k ≤ K + 1) (x w : List Bool) : (hostTM M K hk).tm.step (Cfg.ofWords (input := x) (.inl 0) (stateWord (K + 1) w)) = Cfg.ofWords (hostEntry M 2) (stateWord (K + 1) w)`
  - new: `theorem host_dispatch (M : Fin 5 → FinTM Bool) (K : ℕ) (hk : ∀ i, (M i).k ≤ K + 1) (x w : List Bool) : (hostTM M K hk).tm.step (Cfg.ofWords (input := x) (.inl 0) (stateWord (K + 1) w)) = Cfg.ofWords (ModuleHost.entry M 2) (stateWord (K + 1) w)`
- `Complexity.IterateFind.host_halt` (TCSlib/Complexity/Randomized/Build/IterateFindHost.lean:686->352):
  - old: `lemma host_halt (M : Fin 5 → FinTM Bool) (K : ℕ) (hk : ∀ i, (M i).k ≤ K + 1) (x w o : List Bool) : (hostTM M K hk).tm.step {Cfg.ofWords (input := x) (.inl 2) (stateWord (K + 1) w) with output := o} = {Cfg.ofWords (input := x) (.inl 2 : HostState M) (stateWord (K + 1) w) with state := none, output := o}`
  - new: `theorem host_halt (M : Fin 5 → FinTM Bool) (K : ℕ) (hk : ∀ i, (M i).k ≤ K + 1) (x w o : List Bool) : (hostTM M K hk).tm.step {Cfg.ofWords (input := x) (.inl 2) (stateWord (K + 1) w) with output := o} = {Cfg.ofWords (input := x) (.inl 2 : ModuleHost.State (Fin 3) M) (stateWord (K + 1) w) with state := none, output := o}`

All five follow from item A: `HostState M` → `ModuleHost.State (Fin 3) M`, `hostEntry M i` → `ModuleHost.entry M i`; `hostTM` is an `abbrev` (was `def`), so the generic host lemmas apply to it; `lemma` → `theorem` (no change in meaning).

## Made public (item D)

- `Complexity.polyTimeComputable_stateFind` (TCSlib/Complexity/Randomized/Repetition.lean:241): was `private`; statement unchanged.

## Added

### `TCSlib/Complexity/Randomized/Build/IterateFind.lean`

- `Complexity.IterateFind.step_eq` (theorem, :105)

### `TCSlib/Complexity/Randomized/Build/IterateFindHost.lean`

- `Complexity.IterateFind.hostCtrl` (def, :259)
- `Complexity.IterateFind.hostCtrl_eq` (theorem, :270)
- `Complexity.IterateFind.hostRet_zero` (theorem, :288)
- `Complexity.IterateFind.hostRet_one` (theorem, :292)
- `Complexity.IterateFind.hostRet_two` (theorem, :296)
- `Complexity.IterateFind.hostRet_three` (theorem, :300)
- `Complexity.IterateFind.hostRet_four` (theorem, :304)
- `Complexity.IterateFind.hostTM_eq` (theorem, :317)

### `TCSlib/Complexity/Randomized/Build/PairSplit.lean`

- `Turing.PairParse.cfg` (def, :94)
- `Turing.PairParse.cfg_inputSymbol` (theorem, :100)
- `Turing.PairParse.cfg_congr` (theorem, :112)
- `Turing.PairParse.cfg_workTapeSymbols` (theorem, :121)
- `Turing.PairParse.apply_cfg_stay` (theorem, :130)
- `Turing.PairParse.apply_cfg_advance` (theorem, :141)
- `Turing.PairParse.parse_first` (theorem, :153)
- `Turing.PairParse.parse_block` (theorem, :181)
- `Turing.PairParse.rewind_run` (theorem, :219)

### `TCSlib/Complexity/Randomized/Build/StateLoop.lean`

- `Complexity.StateLoop.gstep_eq` (theorem, :200)
- `Complexity.StateLoop.gstepBound_eval` (theorem, :211)
- `Complexity.StateLoop.IterLoop.start_eq` (theorem, :297)
- `Complexity.StateLoop.IterLoop.step_eq` (theorem, :306)
- `Complexity.StateLoop.IterLoop.acc_eq` (theorem, :315)
- `Complexity.StateLoop.IterLoop.out_eq` (theorem, :323)
- `Complexity.StateLoop.EmitLoop.start_eq` (theorem, :364)
- `Complexity.StateLoop.EmitLoop.step_eq` (theorem, :375)
- `Complexity.StateLoop.EmitLoop.out_eq` (theorem, :387)

### `TCSlib/Complexity/Randomized/Build/StringLoops.lean`

- `Complexity.StateLoop.MajLoop.start_eq` (theorem, :71)
- `Complexity.StateLoop.MajLoop.step_eq` (theorem, :84)
- `Complexity.StateLoop.MajLoop.acc_eq` (theorem, :98)
- `Complexity.StateLoop.MajLoop.out_eq` (theorem, :107)
- `Complexity.StateLoop.XorLoop.start_eq` (theorem, :208)
- `Complexity.StateLoop.XorLoop.step_eq` (theorem, :221)
- `Complexity.StateLoop.XorLoop.acc_eq` (theorem, :236)
- `Complexity.StateLoop.XorLoop.out_eq` (theorem, :245)
- `Complexity.StateLoop.XorLoop.rounds_eq` (theorem, :252)
- `Complexity.StateLoop.EqLoop.step_eq` (theorem, :374)
- `Complexity.StateLoop.EqLoop.out_eq` (theorem, :390)
- `Complexity.StateLoop.EqLoop.flag_eq` (theorem, :400)
- `Complexity.StateLoop.BlockMapLoop.start_eq` (theorem, :524)
- `Complexity.StateLoop.BlockMapLoop.step_eq` (theorem, :537)
- `Complexity.StateLoop.BlockMapLoop.acc_eq` (theorem, :550)
- `Complexity.StateLoop.BlockMapLoop.out_eq` (theorem, :560)
- `Complexity.StateLoop.BlockMapLoop.rounds_eq` (theorem, :569)

### `TCSlib/Complexity/Randomized/Closure.lean`

- `Complexity.NUPPT.exists_compParam` (theorem, :209)

### `TCSlib/Complexity/TuringMachine/Build/ModuleHost.lean`

- `Turing.ModuleHost.first_halt` (theorem, :92)
- `Turing.ModuleHost.live_prefix` (theorem, :111)
- `Turing.ModuleHost.clean_iff` (theorem, :207)
- `Turing.ModuleHost.request_budget` (theorem, :311)
- `Turing.ModuleHost.state_eq` (theorem, :389)
- `Turing.ModuleHost.entry_eq` (theorem, :398)
- `Turing.ModuleHost.hostTM` (def, :409)
- `Turing.ModuleHost.hostTM_step_inl` (theorem, :424)

### Generated by `simps` (`isSimp := false`), not textual declarations

- `Turing.ModuleHost.hostTM_k : (hostTM M K hk ctrl ret q₀).k = K`, `Turing.ModuleHost.hostTM_tm_q₀ : (hostTM M K hk ctrl ret q₀).tm.q₀ = q₀` (`ModuleHost.lean`, at `hostTM`).
- `Complexity.IterateFind.copyTM_k : copyTM.k = 1` (`IterateFindHost.lean`, at `copyTM`).
- `Turing.PairParse.cfg_state`, `cfg_inputPos`, `cfg_workTapes`, `cfg_workTapePos`, `cfg_output` (`PairSplit.lean`, at `cfg`).

## Removed

None besides the moves and renames above. Private declarations deleted (not listed above): SAT's 26-declaration module layer, IterateFindHost's private copy of it, `IterateFind.request_budget`, and UnaryMul's `mulCfg`, `mulCfg_read`, `mulCfg_congr`, `mul_first`, `mul_block` (its `mul_back` is now a one-line instance of `Turing.PairParse.rewind_run`).
