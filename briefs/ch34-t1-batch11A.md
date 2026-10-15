# 12.2c tranche T1 — Batch 11A: one loop host, shared run facts (`Build/Loop.lean` + `TuringMachine/Finite.lean`)

## Repository and branch — read this before anything else

- Clone `https://github.com/Shilun-Allan-Li/tcslib`; check out
  **`complexity/arora-barak-ch3-4`**, NOT `main`. Confirm
  `git merge-base --is-ancestor 9270021ab6499f02b0912bc614fd142761e7339f HEAD`; if it fails, **stop**.
- Branch off fresh (`refactor/12.2c-t1-loop`); record the base hash; never rebase.
- **Delivery by zip**, `12.2c-t1-loop.zip`: `REPORT.md`, both full sources, a
  `git format-patch` series, a bundle, sweep and axiom logs, both screen and
  census outputs, `SHA256SUMS`. Integration (no action for you): 12.2c
  tranche T1 (plan §4e) — side branch, PR for the user, **separate audit gate**.

## What this is

A refactor: no new mathematics, every public statement frozen. Read plan
§4d (items 6, 11) and §4e, the ledger rows "RB4's inlined residue" and CH7-D2,
`rb4-REPORT.md`, `rb5-REPORT.md` §"Withdrawn Loop task", and `policy.md`.

- **12.2c item 11.** The forwarding host `emLoopHost` re-proves the
  `loopHost_*` phases inline (`emLoopHost_round` reproduces 100% of
  `loopHost_reject`, `_prepare` 99%, `_anchor_return` 95%). The two tables
  differ only on body-control states `.inr (.inl (startup, s))`
  (`captureAction` against `leftAction 1 id ∘ Turing.emitAction`). Per-phase
  Z5 transfer is impossible — anchor return starts in body control at
  `t = 0` (`audits/evidence/retrofit/rb5/anchor-return-guard-counterexample.lean.txt`).
  So: one host parametrized by body mode, each phase proved once.
- **CH7-D2, library half.** Three run facts become public in `Finite.lean`;
  Loop's three private copies are deleted. `EmitIterEmbed`'s five become
  citations in T2, not here.

**Pre-ship check (maintainer, executed):** `audits/evidence/ch34-t1/Item11PreShip.lean.txt`
elaborates (0 errors, 0 sorries): Task 1 verbatim; `EmitIterEmbed`'s five and
Loop's call shapes from it; Task 3's host against both tables, every case.

## Owned files (modify these and nothing else)

| File | At the issue commit | May change |
|---|---|---|
| `TuringMachine/Build/Loop.lean` | 5,472 lines, 8 public / 190 private | Tasks 2–4 |
| `TuringMachine/Finite.lean` | 276 lines | Task 1 only |

Lines at the issue commit (Loop unchanged since `5ad155ee`); priority Task 1, 2, 3, 4.

## Task 1 — three public run facts (`Finite.lean`)

Insert verbatim in `namespace Turing.MultiTapeTM`, after
`spaceUsed_le_mul_succ`; no attributes (names unused repo-wide).

```lean
/-- Prepending a fixed word to the output commutes with one step of any machine: the
transition table reads neither the output tape nor its length, and a step only appends
to it. This is the append-only output tape of the machine model [AB09, §1.2] (the
write-only output tape is a declared variation; see `Turing.FinTM`).

**Proof sketch.** A halted configuration does not move. Otherwise both sides apply the
same action, chosen from the unchanged state, input symbol and work-tape symbols; the
output equality is associativity of append. -/
theorem step_output_prepend (tm : MultiTapeTM k Symbol State)
    (cfg : Cfg k Symbol State input) (pre : List Symbol) :
    tm.step { cfg with output := pre ++ cfg.output } =
      { tm.step cfg with output := pre ++ (tm.step cfg).output } := by
  have hi : ({ cfg with output := pre ++ cfg.output } : Cfg k Symbol State input).inputSymbol =
      cfg.inputSymbol := rfl
  have hw : ({ cfg with output := pre ++ cfg.output } :
      Cfg k Symbol State input).workTapeSymbols = cfg.workTapeSymbols := rfl
  cases hs : cfg.state with
  | none => simp [MultiTapeTM.step, hs]
  | some q =>
    simp only [MultiTapeTM.step, hs, hi, hw]
    refine Cfg.ext rfl rfl rfl rfl ?_
    simp only [Action.apply, List.append_assoc]
    rfl

/-- Prepending a fixed word to the output commutes with every run: running from a
configuration whose output already starts with `pre` yields the run's result with `pre`
still in front of its output, halted tails included [AB09, §1.2].

**Proof sketch.** Iterate the one-step commutation `step_output_prepend` along the run
with `runFrom_comm_of_step`. -/
theorem runFrom_output_prepend (tm : MultiTapeTM k Symbol State)
    (cfg : Cfg k Symbol State input) (pre : List Symbol) (t : ℕ) :
    tm.runFrom { cfg with output := pre ++ cfg.output } t =
      { tm.runFrom cfg t with output := pre ++ (tm.runFrom cfg t).output } :=
  MultiTapeTM.runFrom_comm_of_step (tm := tm) (tm' := tm)
    (fun c => { c with output := pre ++ c.output }) (fun c => step_output_prepend tm c pre) cfg t

/-- A run that is still live at time `t` was live at every time `u ≤ t`: the halting
configuration of the model is absorbing [AB09, §1.2].

**Proof sketch.** A halt at some `u ≤ t` would, by `runFrom_add` and `runFrom_of_halt`,
make the configuration at `t` equal to the halted one at `u`. -/
theorem runFrom_state_ne_none_of_le (tm : MultiTapeTM k Symbol State)
    (cfg : Cfg k Symbol State input) (t : ℕ) (ht : (tm.runFrom cfg t).state ≠ none) :
    ∀ u ≤ t, (tm.runFrom cfg u).state ≠ none := by
  intro u hu hh
  have he : tm.runFrom cfg t = tm.runFrom cfg u := by
    rw [← Nat.add_sub_of_le hu, MultiTapeTM.runFrom_add, MultiTapeTM.runFrom_of_halt _ hh]
  exact ht (by rw [he]; exact hh)
```

Add one *Main results* bullet after `spaceUsed_le_mul_succ`'s: the three names —
"runs commute with a fixed output prefix, and a live endpoint has a live past
(shared run facts, 12.2c/CH7-D2; added 2026-10-10)". Keep the `runFrom_comm_of_step`
proof (re-typing `emLoop_run_prefix`'s induction would carry its 46 cross-file and
18 in-file idiom pairs into Finite). The three ride this batch's gate.

## Task 2 — Loop's copies, the rider, the alias (4803, 4897 go with Task 3)

| Delete (docstring + declaration) | Lines | Each use becomes |
|---|---|---|
| `loop_live_prefix` | 186–195 | 1376: `MultiTapeTM.runFrom_state_ne_none_of_le body.tm c t (by rw [hend]; simp)` |
| `emLoop_step_prefix`, `emLoop_run_prefix` | 4610–4639 | 5164: `MultiTapeTM.runFrom_output_prepend (emLoopHost body F anchor true).tm admin chunk v`; 5203: `MultiTapeTM.runFrom_output_prepend tm (cfg 0) pre a` (`cfg` before `pre`) |
| `loop_input_move_le`, `loop_input_run_le` | 241–269 | 1318: `MultiTapeTM.timed_input_bound (tm := F.tm) (F.tm.initCfg x) u` |
| comment + `local notation "emCall_state_run"` | 182–184 | 4227: the token becomes `MultiTapeTM.runFrom_mapState_of_agreeOn` (`emCall_bank_step`'s statement and docstring byte-identical) |

## Task 3 — one body-mode-parametric host

Replace `loopHost` (594–678) by the following, its docstring moving to
`loopHostM`:

```lean
/-- Body dispatch of the shared loop controller: `forward = false` captures body
emissions on the payload tape (`Turing.captureAction`); `forward = true` forwards them
to the physical output (`Turing.emitAction`), payload tape stationary. -/
private def loopBodyDispatch (body F : FinTM Bool) (anchor : body.State) (forward : Bool)
    (startup : Bool) (s : body.State × Bool) (inp : Option Bool)
    (work : Fin (body.k + 1 + (1 + F.k) + 1) → Option Bool) :
    Action (body.k + 1 + (1 + F.k) + 1) Bool (LoopHostState body F) :=
  bif forward then
    leftAction 1 id (Turing.emitAction (fun s => .inr (.inl (startup, s)))
      (.inr (.inr (if startup then 6 else 7)))
      ((loopBodySource body F anchor).tr s inp (fun i => work i.castSucc)))
  else
    captureAction (fun s => .inr (.inl (startup, s)))
      (.inr (.inr (if startup then 6 else 7)))
      ((loopBodySource body F anchor).tr s inp fun i => work i.castSucc)

private def loopHostM (body F : FinTM Bool) (anchor : body.State) (forward findMode : Bool) :
    FinTM Bool where
  -- lines 607–621 verbatim; then
  -- `| .inr (.inl (startup, s)) => loopBodyDispatch body F anchor forward startup s inp work`;
  -- then `| .inr (.inr phase) =>` and lines 626–678 verbatim (MOVE the block, never retype)

private abbrev loopHost (body F : FinTM Bool) (anchor : body.State) (findMode : Bool) :
    FinTM Bool := loopHostM body F anchor false findMode

/-- The host image of a padded stopped-body configuration in either mode. -/
private def loopBodyImage (body F : FinTM Bool) (forward startup : Bool) (pre : List Bool)
    {x : List Bool} (d : Cfg (body.k + 1 + (1 + F.k)) Bool (body.State × Bool) x) :
    Cfg (body.k + 1 + (1 + F.k) + 1) Bool (LoopHostState body F) x :=
  bif forward then
    emLoopForwardCfg (fun s => .inr (.inl (startup, s)))
      (.inr (.inr (if startup then 6 else 7 : Fin 14))) pre d
  else
    captureCfg (fun s => .inr (.inl (startup, s)))
      (.inr (.inr (if startup then 6 else 7 : Fin 14))) [] pre d
```

- **Placement.** `emLoopHost` (4644) becomes
  `private abbrev … := loopHostM body F anchor true findMode` (docstring kept).
  Move `emLoopForwardCfg`, `emLoopCall`, `emLoopCall_frame` (4811–4847) and
  `emLoopCall_empty` (4920–4931) unchanged to after `loopCall` (1338), then
  `loopBodyImage`, then `loopBodyImage_nil`:
  `loopBodyImage body F forward startup [] (loopBodyPadded body F anchor c release flag word fuel) = loopCall body F anchor startup c release flag word fuel`
  under `c.output = []` (by `cases forward`: `rfl` / `emLoopCall_empty`).
- **Fuel/controller phases, generalized in place, proofs unchanged.** Insert
  `(forward : Bool)` after `(anchor : body.State)` and write
  `loopHostM body F anchor forward findMode` for `loopHost …` in
  `loopHost_fuel_capture` (696), `_init` (708; add `loopHostM` to the simp set
  at 714), `_input_rewind` (725), `_fuel_copy` (1073), `_fuel_setup` (1179),
  `_prepare` (1288), `_release` (1443), `_borrow_step` (1580), `_borrow_run`
  (1618), `_borrow` (1701), `_reject` (1743) and Task 4's three scan lemmas.
  The `.inl` and phase branches never mention `forward`, so every
  `change (loopControlAction …).apply _ = _` still holds (probe-checked); if
  one fails, escalate, do not restructure. Internal citations pass `forward`;
  capture-only callers (2020, 2106, 2179, 1955) pass `false`. Capture-only
  statements stay: `_replay`, `_frame_replay`, `_accept`, `_halt_return`,
  `_round`, `_contracts`, `_bound`.
- **Body phases, proved once.** Delete `loopHost_body_capture` (680–693). Add
  `loopHost_body_run (forward findMode startup : Bool) (pre : List Bool) (d) (t) (hlive : ∀ u < t, ¬((loopBodySource body F anchor).runFrom d u).Halted) : (loopHostM body F anchor forward findMode).tm.runFrom (loopBodyImage body F forward startup pre d) t = loopBodyImage body F forward startup pre ((loopBodySource body F anchor).runFrom d t)`
  — the only place the hosts differ. Proof by `cases forward`: capture is
  `exact capture_run (loopBodySource body F anchor) (loopHostM body F anchor false findMode).tm _ _ (by intro s inp work; rfl) [] pre d t hlive`;
  forward is the inlined `emLoopHost_body_forward` proof (4877–4895), simp
  set extended by `loopHostM, loopBodyDispatch`.
- **`loopHost_anchor_return` (1363)**, generalized in place with
  `(forward findMode startup : Bool) (pre : List Bool)`; conclusion
  `(loopHostM … forward findMode).tm.runFrom (loopBodyImage body F forward startup pre (loopBodyPadded body F anchor c release none word fuel)) (t + 1) = loopBodyImage body F forward startup pre (loopBodyPadded body F anchor {body.tm.runFrom c t with state := none} false (some false) word fuel)`.
  Proof: keep 1375–1390, then `unfold loopBodyPadded; rw [loopHost_body_run]`
  and the two closing bullets. Callers recover `loopCall`/`emLoopCall` forms
  by defeq, never `rw`: `loopHost_round`'s `change … at hcap` (2017) spelled
  out; `loopBodyImage_nil` in `loopHost_start`; `change … at hr` in
  `emLoopHost_round`.
- **`loopHost_start` (1474)**, over `forward`, conclusion unchanged: take
  `loopHost_anchor_return … forward findMode true []` at `body.tm.initCfg x`,
  rewrite it by `loopBodyImage_nil` on both sides (`hend` between), then
  `rw [loopReady_call …, t + 2 = (t + 1) + 1, runFrom_succ_eq_step', hr, loopHost_release]; rfl`.
- **`loopHost_halt_return` (1494)**, statement unchanged: `change` both sides
  to `loopBodyImage body F false false [] (loopBodyPadded …)` form, then
  `unfold loopBodyPadded; rw [loopHost_body_run]`.
- **Forwarding family.** Delete `emLoopHost_agree` (4658–4669), `_prepare`
  (4671–4809), `_anchor_return` (4849–4918), `_start` (4933–4963) and their
  inlined `have`s. `emLoopHost_round` (4972) keeps statement and docstring,
  loses its inlined reject/borrow (4990–5146), and its tail takes
  `hr := loopHost_anchor_return body F anchor true true false [] c true t word fuel …`, then
  `change (emLoopHost body F anchor true).tm.runFrom (emLoopCall body F anchor [] false c true none word fuel) (t + 1) = emLoopCall body F anchor [] false {body.tm.runFrom c t with state := none} false (some false) word fuel at hr`
  (the existing `rw [emLoopCall_empty …, hend, emLoopCall_frame] at hr` then
  applies), and `loopHost_reject body F anchor true true …` for
  `emLoopHost_reject body F anchor true …`.

## Task 4 — the rewind scans and the glue

```lean
/-- A leftward scan, for any machine: if each step from `frame (j + 1)` with `j < n`
lands on `frame j`, and the step from `frame 0` lands on `done`, then `j + 1` steps
from `frame j` reach `done` for every `j ≤ n`.
**Proof sketch.** Induction on `j`, one step at a time. -/
private lemma loop_scan_left {k : ℕ} {S : Type*} {x : List Bool}
    (tm : MultiTapeTM k Bool S) (frame : ℕ → Cfg k Bool S x) (done : Cfg k Bool S x) (n : ℕ)
    (hstep : ∀ j < n, tm.step (frame (j + 1)) = frame j)
    (hexit : tm.step (frame 0) = done) :
    ∀ j ≤ n, tm.runFrom (frame j) (j + 1) = done
```

1. **`loopHost_payload_scan`** replaces `loopHost_fuel_rewind` (979) and
   `loopHost_payload_rewind` (1815) — identical up to phases 1→2 / 12→13 (the
   100%/99% pair). Statement: `_fuel_rewind`'s with `(src dst : Fin 14)` for
   1/2 and
   `(htr : ∀ inp work, (loopHostM body F anchor forward findMode).tm.tr (.inr (.inr src)) inp work = match work (Fin.last (body.k + 1 + (1 + F.k))) with | some _ => loopControlAction body F 0 none (none, 0) (none, .neg) none (some (.inr (.inr src))) | none => loopControlAction body F 0 none (none, 0) (none, .pos) none (some (.inr (.inr dst))))`.
   Proof: `loop_scan_left` at
   `frame j := loopFrame … (some (.inr (.inr src))) … ((j : ℤ) - 1) out`;
   `hstep` is the old `hs` block with `change` replaced by
   `show ((loopHostM …).tm.tr _ _ _).apply _ = _; rw [htr]`; `hexit` the old
   `zero` case. Callers: `_fuel_setup` `1 2 (fun _ _ => rfl)`; `_accept`
   `false true 12 13 (fun _ _ => rfl)`.
2. **`loopHost_fuel_return` (1124), `loopHost_borrow_rewind` (1651)**:
   statements change only by `forward`; re-prove each by `loop_scan_left`,
   keeping only its own step and exit computations.
3. **`loopCall_frame` (1521)** becomes
   `(loopCall_reframe body F anchor c startup startup release release flag flag word word fuel c.state).symm`
   (the 95% pair; `exact`, since `{c with state := c.state}` is `c` by eta).

## Sanctioned public changes (complete)

The 8 publics are byte-identical (statements, bodies, docstrings) except in
`exists_emitLoopTM`: 5296–5297 `emLoopHost_prepare body F anchor true R T hF x`
→ `loopHost_prepare body F anchor true true R T hF x`; 5332–5333
`emLoopHost_start body F anchor true (s0 x) btime fuel hbguard hbend` →
`loopHost_start body F anchor true true …` (same arguments); and the docstring
at 5261, `` `emLoop_run_prefix` `` → `` `Turing.MultiTapeTM.runFrom_output_prepend` ``.
If a `rw` there no longer matches through `let E`, insert `simp only [E]` and
list it. No private wrappers; any other public change is an escalation.

## Ground rules (binding)

1. **Ownership**: the two files (Finite: Task 1 only); **imports**: none;
   **freeze** as above — list every private whose statement changed, before/after.
2. **No parallel copies**: the table exists once, in `loopHostM`; no
   `emLoopHost_*` restates a generalized lemma.
3. **Escalation**: if a prescribed generalization fails, restore that phase's
   base form byte-identically, record why, continue. Never weaken a statement.

## Duplication governance (binding; measured on text)

```sh
python3 -I audits/evidence/retrofit/copy-text-screen.py <repo-root> \
  TCSlib/Complexity/TuringMachine/Build/Loop.lean \
  TCSlib/Complexity/TuringMachine/Finite.lean \
  TCSlib/Complexity/TuringMachine/Deterministic.lean \
  TCSlib/Complexity/TuringMachine/Build/EmitIterEmbed.lean \
  TCSlib/Complexity/TuringMachine/Build/Catalog.lean
```

Baseline (recompute at your base): 596 declarations / 673 pairs / 280,141 chars;
Loop→Loop 110 / 56,666, Loop→Catalog 115 / 59,686, Catalog→Loop 161 / 63,588.

- **Loop in-file pairs and characters must fall**, and these must go: the
  `emLoopHost_*`→`loopHost_*` pairs (including `emLoopHost_round`'s with
  `_borrow*`, `_fuel_return`, `emLoopHost_start`); the 18 pairs involving
  `emLoop_run_prefix`; `_payload_rewind`↔`_fuel_rewind`;
  `loopCall_reframe`→`loopCall_frame`.
- **No new cross-file pair except carry-over**: its Loop side absorbed a
  named deleted or renamed declaration (`loopHostM`←`loopHost`,
  `loopHost_body_run`←`loopHost_body_capture`,
  `loopHost_payload_scan`←`_fuel_rewind`/`_payload_rewind`), its partner
  paired with that declaration at baseline, and its share is no higher. List
  each.
- **Report, never ship silently,** every new pair involving `loop_scan_left`,
  `loopBodyDispatch`, `loopHostM`, `loopBodyImage(_nil)`, `loopHost_body_run`
  or `loopHost_payload_scan` (both sides, share), and `loopHost_fuel_copy`'s
  disposition either way; any pair touching Task 1 (none expected). Justify
  every other new in-file pair; ≥ 90% is a copy — factor it.
- **Census**: `python3 -I audits/evidence/retrofit/r1-public-proof-screen.py <repo-root>` before/after; pass 4 Loop ≤ 98.

## Environment and verification

- Lean 4 v4.25.0, mathlib pinned; `lake exe cache get`; **never `lake
  build`**; check everything with `scripts/lean_check_tree.sh`.
- **Bootstrap** once from `briefs/orders/ch34-t1-loop.txt`, line by line in
  order. It is the dependency-ordered upstream closure of the owned files and
  of the replay set (every campaign module downstream of `Loop`, and every
  direct importer of `Finite`), the replay set included; `TCSlib` and
  `TCSlib/ComputationalModels` are excluded. Record the base sorry warnings;
  iterate per edit on `Loop`.
- **Final**: `Finite`, `Loop` — 0 errors, 0 sorry warnings; every later
  module of the order list — 0 errors, sorry warnings exactly the base's. The
  maintainer replays Finite's full 205-module closure at integration.
- **Axioms**: Loop's 8 publics (`Turing.stateWord`, `Turing.loop_run`,
  `Turing.FinTM.exists_{loopCfgTM, loopTM, loopFindTM, emitLoopTM, installCallTM, emitCallTM}`)
  byte-identical to base; Task 1's three within the standard triple; no `sorryAx`.
  **Lint**: `python3 scripts/campaign_style_lint.py` on `TCSlib/Complexity/TuringMachine` and `…/Build`, 0 FAIL.

## Out of scope (record, do not fix)

- **11B** (after the G1 gate): the `emCall*` cluster (40 pairs / 24,078
  characters, on Embed's frames); `loop_run`/`loop_halted_run`/`loop_find_run`;
  the `exists_*` body parallels. **T2** (ch7 owner): `EmitIterEmbed`'s five;
  item 6 owns `loopBodyTM`/`loopBodyCfg` ↔ `padAction`/`embedCfg`.
- **Later citations of Task 1** (list in `REPORT.md`): Catalog
  `f2_loop_live_prefix`, Hardness `clA5_live_prefix`, SAT `sat_live_prefix`,
  Catalog `f2_loop_input_*` and the `f2_loopHost*` twins (item 1).
- **Item 12**: Loop cannot import `CounterLoop` (→ `Catalog` → `Loop`); the
  fuel-debit re-derivation waits for T3's layout. **G1** owns
  `Simulation`/`Embed`/`Seam`/`Catalog` — never touch them. Leave
  `loopHost_contracts`'s historical docstring (2034–2052).

## REPORT.md checklist

- [ ] Base hash, ancestor check; Tasks 1–4 status; line and private deltas.
- [ ] Every added/deleted/moved/`def`→`abbrev` declaration; every changed
      private statement (before/after); the sanctioned public edits, quoted.
- [ ] Screen before/after with the removed-pair checklist, carry-overs,
      reported pairs and the `fuel_copy` disposition; census before/after.
- [ ] Escalations or "none"; sweep tail; 11 axiom prints; 2 lint lines; diff
      touches only the two owned files.

## Known pitfalls at this pin (hard-won)

- **`rw` matches at reducible transparency**: it sees through the `abbrev`s
  and `let E`, not through the `def`s `loopCall`, `emLoopCall`,
  `loopBodyImage` or `bif` on a literal — use a typed `have`/`change` there.
- **Matchers**: within one module, `match`es of one shape share a matcher,
  so `fun _ _ => rfl` should discharge `htr`. Fallback: split `htr` into a
  `work (Fin.last _) = some b → …` and a `… = none → …` hypothesis, each
  discharged by `change` and `rw`. Move the table; never retype it.
- **Mode and casts**: `cases forward` before needing one branch;
  `((j + 1 : ℕ) : ℤ) - 1 = (j : ℤ)` by `omega`; `frame 0` is `((0 : ℕ) : ℤ) - 1`
  (`Nat.cast_zero` before `zero_sub, bufferTape_left`). Payload `Fin.last (body.k + 1 + (1 + F.k))`, counter `⟨body.k + 1, by omega⟩`, flag `⟨body.k, by omega⟩`.
- **Names**: write `Turing.emitAction` for E2 (in `Turing.FinTM`, plain
  `emitAction` is Simulation's); `runFrom_of_halt` takes `tm` implicitly;
  `runFrom_succ_eq_step` peels the front, `…_step'` the back.
