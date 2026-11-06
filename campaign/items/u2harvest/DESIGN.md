# U2 harvest API (`lean/u2-harvest-api`): design

Base: `origin/complexity/arora-barak-ch3-4` at `205bbdbe` (Lean tree equal to `a28b8c42`, the
`oleans-lcamp2` replay's tree). Source: `TCSlib/Complexity/TuringMachine/UniversalK.lean`
(2,873 lines). Ruling (user, 2026-11-06): the harvested rows go in a **new `Build/` module**;
`UniversalK` imports it; `universalK`'s and `exists_selfUniversalK`'s statements are
byte-identical.

## 1. The module

**`TCSlib/Complexity/TuringMachine/Build/UniversalParts.lean`**, namespace `Turing` (the forwarding
loop's rows under `Turing.StepBlock`, beside H2-F's names), private prefix `up_`.

*Why this name.* The module holds the four groups of parts the `k`-generic universal machines are
assembled from: the header ruler (a scan of a doubled header writing one ruler cell per input cell,
then the rewind), the startup–loop seam with its time and space readings, the forwarding loop's
corollaries at an initial configuration, and the suffix-ruler layout that joins the first three to
the ruler host. `HeaderScan` would name only the first group; the four have one purpose (the
universal machines U2-U, U2-E and next F6's `SU`). The name follows the directory's
noun-phrase style and parallels `Build/InterpreterStartup` ("the pieces of a universal machine's
startup").

*Imports (minimum, computed from header imports).* Three `TCSlib` modules, none in another's
closure, none reaching `UniversalK`, plus one Mathlib module found at elaboration
(`Mathlib.Algebra.Group.Action.Defs`, for `smul_eq_mul` in the `Finset.sum_const` steps;
`UniversalK` had it through `Codes2Tape`/`Clean`):
- `Build.StepBlockForward` — `StepBlock.forwardLoopCfg` and its field equations, `Lockstep`
  (`Contract/Basic`), `summaryCells_eq`, `tableBitsK`, and in its closure `Seam`, `Embed`,
  `Catalog` (`tapeAction`, `inputMoveAction`, `step_of_tapeAction_write`), `Encoding`
  (`pairEncode`, `length_pairEncode`, `unaryFin`), `Simulation` (`FinTM.bufferTape`), `Finite`;
- `Build.InputDevice` — `rulerHostCfg` and its field equations;
- `Build.Rewind` — `rewindTM`, `RewindPhase`, `rewindTM_run_ofCfg`.

`UniversalK` keeps its seven imports and gains `Build.UniversalParts` (no cycle: the new module's
closure is 20 + 19 + 15 modules of the `Build` layer, without `UniversalK`, `UniversalStartup`'s
consumers or `Codes2Tape`). Size: 976 lines (target band 150–600 is exceeded; under 1000;
reported, not split, because the four groups cite one another: the suffix layout's embedding
lemma reads the forwarding rows, the space ledger reads the seam rows).

## 2. The rows (each: final statement, source, what moves with it)

Notation: `σ := Fin.castLEEmb (_ : k + 2 ≤ K + (k + 2))`; `blank₀ := embedEmitCfg σ (fun _ _ =>
none) (fun _ => 0) []`.

### 2a. The restart identity (RS-1) — see §5 Q1
- **`Turing.MultiTapeTM.initCfg_eq_mapState`** ← `uk_init_mapState` (private, :1816). Statement
  unchanged: `B.q₀ = f A.q₀ → B.initCfg x = (A.initCfg x).mapState f` (binary alphabet). Needed by
  `startupLoopTM_initCfg` (new module) **and** by `uk_suffixStartup_run` (stays in `UniversalK`).

### 2b. The forwarding loop at an initial configuration (`Turing.StepBlock`)
- **`StepBlock.forwardLoopCfg_init_workTapes`** ← `uk_encode_init_tapes` (:1697). Unchanged.
- **`StepBlock.forwardLoopCfg_init_fields`** ← `uk_encode_init_fields` (:1736). Unchanged.
- **`StepBlock.forwardLoopCfg_halt_iff`** ← `uk_encode_halt` (:1752). Unchanged (an iff and the
  output equation, as a conjunction).
- **`Turing.embedEmitCfg_forwardLoop_init`** ← `uk_embed_init` (:1766). Unchanged: `blank₀
  (forwardLoopCfg entry M (M.initCfg x))` is the startup's native endpoint layout relabelled at
  `entry`.
- **`StepBlock.forwardLoop_forward`**, **`_live`**, **`_converse`** ← `uk_loop_forward` (:1871),
  `uk_loop_live` (:1896), `uk_loop_converse` (:1918). Unchanged; generic in `M`, `L`, `cost`.

### 2c. The startup–loop seam
- **`Turing.startupLoopTM R exit L entry`** ← `uk_loopTM` (:1807), a machine: `{ seamCompTM R exit
  (embedEmitTM σ L) entry with q₀ := Sum.inl R.q₀ }`. Read through its run lemmas (policy §1).
- **`startupLoopTM_initCfg`** ← `uk_loop_init` (:1827); **`startupLoopTM_live_of_le`** ←
  `uk_loop_pre_live` (:1834); **`startupLoopTM_runFrom`** ← `uk_loop_run` (:1850). Unchanged.
- **`startupLoopTM_spaceUsed_le`** ← `uk_loop_space` (:1954), **generalized** (plan §F6(c)):
  ```
  (c : Cfg (k + 2) Bool Q x) (d : Cfg (K + (k + 2)) Bool P x) (T : ℕ)
  (hrun : R.runFrom (R.initCfg x) T = d) (hexit : d.state = some exit)
  (hcut : ∀ u < T, (R.runFrom (R.initCfg x) u).state ≠ some exit)
  (hcfg : d.mapState (fun _ => entry) = blank₀ c)
  (t B S : ℕ) (hB : R.spaceUsed (R.initCfg x) T ≤ B) (hS : 1 ≤ S)
  (hloop : ∀ i, L.spaceUsedByTape c t i ≤ S) :
  (startupLoopTM R exit L entry).spaceUsed (…initCfg x) (T + 1 + t) ≤ B + (K + (k + 2)) * S
  ```
  i.e. for **any seam endpoint** `d` and loop start `c`, exactly `startupLoopTM_runFrom`'s seam
  hypotheses. *Argument:* the old proof read the fixed endpoint only through `uk_embed_init`
  (its `he : d.mapState (fun _ => entry) = e`) and through `d.state = some exit` (`rfl`); both are
  now hypotheses, and `M` disappears. At `d :=` the native layout and `c := forwardLoopCfg entry M
  (M.initCfg x)`, `hexit` is `rfl` and `hcfg` is `embedEmitCfg_forwardLoop_init`, which is the old
  statement. At `(K, k + 1)` with `d := suffixRulerCfg …` and `c := rulerHostCfg …` it is the
  suffix layout F6 needs.

### 2d. The header scan and the header ruler
- **`Turing.headerScanTM i`** ← `uk_scanTM` (:2161). A machine, read through `headerScanTM_run`.
- **`Turing.headerScanCfg i d q t ht`** ← `uk_scanCfg` (:2170), with
  `attribute [simps (config := { isSimp := false }) state inputPos workTapes workTapePos output]`:
  `headerScanCfg_state`, `_inputPos`, `_workTapes` (pointwise), `_workTapePos`, `_output`.
- **`headerScanTM_run`** ← `uk_scan_run` (:2370). Unchanged (any input offset `1 + p` with
  `z.drop p = pairEncode u v`, any ruler head): the endpoint `headerScanCfg i d 3 (2|u|+2)`, the
  first-return cut and silence.
- **`headerScanCfg_ruler`** ← `uk_scan_ruler` (:2397), **generalized** to an existing ruler prefix:
  ```
  (m : ℕ) (hpre : ∀ a : ℤ, d.workTapes i (d.workTapePos i - m + a) =
      FinTM.bufferTape (List.replicate m true) a) :
  ∀ a : ℤ, (headerScanCfg i d q t ht).workTapes i (d.workTapePos i - m + a) =
      FinTM.bufferTape (List.replicate (m + t) true) a
  ```
  *Argument:* `hpre` says the tape is exactly `true^m` ending just before the head (blank
  elsewhere). The scan marks `[pos, pos + t)` and keeps every other cell, so the tape becomes
  `true^(m + t)` from the same start. At `m = 0`, `hpre` is equivalent to the old `hblank`
  (`bufferTape [] = none`) and the conclusion is the old one up to `Nat.cast_zero`, `sub_zero`,
  `zero_add` (the private corollary `up_scan_ruler_blank` restates it, used by
  `headerRulerTM_run`). Two scans compose: after the first, the head is at `pos + ℓ₁` and
  `(pos + ℓ₁) - ℓ₁ = pos`, so the second scan's `hpre` at `m = ℓ₁` is the first's conclusion,
  giving `true^(ℓ₁ + ℓ₂)` (checked in the probe).
- **`Turing.headerRulerTM i`** + **`headerRulerTM_run`** ← `uk_headerTM` (:2414), `uk_header_run`
  (:2424). Unchanged (scan from a blank ruler tape, then the rewind).
- Moving with them, renamed: `uk_scan_zero/step/pair/header` → private `up_scan_zero`,
  `up_scan_step`, `up_scan_pair`, `up_scan_header`; new private `up_scan_ruler_blank` (the
  `m = 0` corollary, derived, not a copy).

### 2e. The suffix-ruler layout
- **`Turing.suffixRulerCfg q M z ℓ hℓ`** ← `uk_suffixCfg` (:2504), generic in `z`, `ℓ`, with
  `simps` field equations (`suffixRulerCfg_state`, `_inputPos`, `_workTapes`, `_workTapePos`,
  `_output`, no `simp` attribute).
- **`Turing.rulerHostCfg_fields`** ← `uk_ruler_fields` (:2651). Unchanged.
- **`Turing.suffixRulerCfg_embed`** ← `uk_embed_suffix` (:2672). Unchanged.

None of the plan's rows has to sit beside its host's definition: the corollaries of
`forwardLoopCfg` and `rulerHostCfg` read them only through their published `simps` equations
(and `summaryCells_eq`), so they all go in the new module, as the ruling asks.

## 3. Rule-10 cases (a proof unfolding a definition that is now in another file)

Moved code: its own definitions move with it (`headerScanTM`, `headerScanCfg`, `headerRulerTM`,
`startupLoopTM`, `suffixRulerCfg`), so its unfoldings of them stay own-file; it reads no definition
that stays in `UniversalK`; its reading of other files' definitions is unchanged by the move.

`UniversalK`'s remaining proofs are now consumers of the moved definitions:
1. **`uk_suffixStartup_run`, step `final`** unfolds `uk_suffixCfg` five times: `rfl` on `.state`,
   `change c.inputPos.val + ℓ = ℓ + 1` on `.inputPos`, `simp only [… uk_suffixCfg …]` on
   `.workTapes` (both branches), `rfl` on `.workTapePos` and `.output`. **Fix:** rewrite with
   `suffixRulerCfg_state`, `_inputPos`, `_workTapes`, `_workTapePos`, `_output`.
2. `uk_suffixStartupTM` mentions `uk_headerTM` only as a machine argument; `uk_suffixStartup_run`
   reads it through `uk_header_run` only. No unfolding (re-pointed by name).
3. `exists_selfUniversalK`, `universalK`: `uk_loopTM` only as `tm := …` and through the run,
   live and space lemmas; `U.tm` reduces the local structure, not `startupLoopTM`. No unfolding.
4. **`universalK`'s body** (found by the seal probe, missed by reading): `uRun` passed `rfl` for
   `(uk_suffixCfg …).state = some finish`, and `hprefix` closed `(uk_suffixCfg …).state ≠ none`
   by `Option.some_ne_none` through the definition. **Fix:** `suffixRulerCfg_state` in both.
   A body change of `universalK`, statement unchanged.
Verification (done): a seal probe — `UniversalK` with the five moved definitions `[local irreducible]`
(controls: an `rfl` per definition failing sealed, closing unsealed) — and the new module with the
other-file definitions it reads sealed.

## 4. What stays in `UniversalK`

Lines 1–1688 unchanged (`EffectiveCodeK`, the instances, the `ss_*` startup kit,
`exists_selfStartupTMK`) apart from the import and the module docstring; `exists_selfUniversalK`
(body re-pointed); `uk_suffixStartupTM` and `uk_suffixStartup_run` (private, U2-E's own native
startup composition; re-pointed, rule-10 fix 1); `universalK` (body re-pointed). Deleted (moved):
the 26 privates listed above (`uk_init_mapState` included, §5 Q1). Result: 2,873 → 2,127 lines (12 public, 67 → 41 private); the new module 976 lines (22
public, 5 private).

## 5. Open points for the user

- **Q1 (RS-1).** `uk_init_mapState` is needed on both sides of the cut. Two options: (A,
  implemented) publish it in the new module as `Turing.MultiTapeTM.initCfg_eq_mapState`; RS-1 stays
  at five sites, and the ledger's disposition (a row beside `initCfg_with_q₀` in `Finite`) becomes a
  move of a public lemma with its name kept; (B) a private copy in the new module, RS-1 five → six
  sites, a disclosed new copy. The plan's D-F6-5 said "keep RS-1 out of the harvest", written for
  the in-place home, where no copy arose. Switching to (B) is a ten-line change.
- **Q2 (optional).** `headerRulerTM_run` keeps its blank-tape hypothesis (visibility only, per the
  plan). F6's second header (scan from the ruler's end, then rewind over `true^(ℓ₁ + ℓ₂)`) composes
  `headerScanTM_run`, `headerScanCfg_ruler` and `rewindTM_run_ofCfg` itself; a generalized
  `headerRulerTM_run` from a prefix `true^m` was not asked for and is not added.
