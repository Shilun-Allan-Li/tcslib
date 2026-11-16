# R4 design and sizing study: the SAT/Hardness families

**Answers** `campaign/closeout/r4-design-request/brief.md` (2026-11-16). Read-only study: no Lean or
`lake` run, no Lean file edited, no pull request.

**Inputs.** `arora-barak-ch3-4/outbox/fills/r4-design/r4-design-bundle.md`, SHA-256
`d8da8a458f3d32819b89ed13e131cc44fc1d20c60a92db3528fe7d18b3c6877a`. It matches `SHA256SUMS`, as do
`README.md` and `maintainer-inventory-R4.json` (`3efe67b8…aeda`). It has 15 sections in
`BUNDLE-FILES.txt` order and is 1,335,325 bytes. Lean sources are at `68cba664`; the records are
at `4211cada`. The extracted Lean files have the plan's sizes: `ClassNP/SAT.lean` 4,370 lines and
270 declarations (264 private), `CookLevin/Hardness.lean` 8,701 lines and 544 declarations (539
private), `TuringMachine/Finite.lean` 516 lines. `Hardness` imports `SAT` directly (`Hardness:8`).

**Measured or estimated.** *Measured* means read off the three bundled Lean files: declaration
spans, line numbers, twin comparisons, mentions, and the read forms in proof text. *Estimated*
means anything about code that does not exist yet: interfaces, adapters, equations, repairs and
net totals. Every estimate is a range and is marked "est.". Line conventions follow the
inventory's: a span runs from the header (or its `@[…]` line) to the last non-blank line, with the
docstring counted separately and written `code+doc`. The method is in §10.

---

## 1. Summary table

"Net" means Lean lines in `SAT` + `Hardness` + new modules + other owners' files, after minus
before. Removed lines are measured and added lines are estimated, so every net figure is an
estimate. "Pairs" are twin correspondences between the two files (and one-sided instances of an
acknowledged kind), not copy-screen output, which cannot be run here.

| Family | Members | Use sites (touched) | Net lines | Pairs retired / created | Rule-10 repairs | New public API | Statement changes | Recommendation |
|---|---|---|---|---|---|---|---|---|
| **SG1-A** · kind 4, one-way transducer (+ riders `satScan*`, `clFill*`, `sat_pt_head/tail`) | 10 exact (5 pairs; 71 lines/side) + 3 one-sided riders (155 lines) | 1 (+0 with names kept) | **est. −150 to −80** (−30 to +15 without riders) | 5 + 2 one-sided residues + 2 one-sided instances / 0–2 | 2 moved proofs + 1 use site | yes: one module (word semantics, machine, linear-time and poly-time contracts, 2 equations) | none public; no private one either if names kept | **Run** (PR R4-1, pilot) |
| **SG1-B** · kinds 1, 2, 5 (+ riders `live_prefix`, `guard_add`, FH twin) | 12 pairs, 24 decls (184 lines/side; 368 total) | 4 (126 lines) + a rename in `clA5Modules` | **est. −80 to +50** | 12 / 0–3 | 5 moved proofs + 4 use sites | yes: clean-module contract, release-stop adapter (≈8 public decls + simps) | none public; private headers byte-identical through aliases | **Run with a stop rule** (PR R4-2) |
| **SG1-C** · kinds 3, 6 (bank padding, finite-family dispatcher) | 13 pairs, 26 decls (154 lines/side; 308 total) | 4 (323 lines) | **est. −90 to +35** time-only; **+10 to +335** with a head-envelope clause | 13 / 0–3 | 5 moved proofs + 4 large use sites | yes: a public **host** (needs registry entry, time + envelope clauses by policy) | none public; private statements of `clA5Startup`/`clA5Round` change | **Carry by default**; run (PR R4-3) only if Seyoon accepts a time-only host contract |
| **SG1-UH** · unary-clock host | 14 Hardness-only (293+43) | 3 outside (75 lines) | **est. +170 to +370** | 0 (no copy) / 0–3 | 14 + 3 | yes: host contract with envelope clauses (B1040) | none | **Carry** (no second consumer; see §4) |
| **PL-1** twins | 2 in bundle (`sat_pt_eq`, `clA5_pt_eq`, 7+2 each) + 2 in `Nondeterminism` (not bundled) | 7 (0 with names kept) | **est. −8** in bundle (−5 to −8 more in `Nondeterminism`, unverified) | 1 (+1 vs public rows) / 0 | 0 | none (possible import of `Build/WordTests` into `SAT`, flag) | none | **Run** (rides PR R4-1) |
| **12.2c item 13** · `clPlacement` | 17 layer (209+32) + 9 selectors (44+9) + 2 attribute lines = 296 | 42 (1,112 lines) | **est. −160 to +215** | 0 (not copy debt) / 0–9 | 42 touched proofs (117 `rfl`, 21 `change`, many foreign `simp` reads) | none, or one combinator in `Build/Embed` | none | **Carry** (register; pilot one layout only if Seyoon wants a measurement) |
| **FH-1 held** | in bundle: 1 exact twin pair (13+3 each; counted in SG1-B) and `sat_first_halt` (already a citation); the 7 held implementations are **outside SAT/Hardness** | — | 0 beyond SG1-B | (in SG1-B) | — | at most `MultiTapeTM.exists_first_halt_pos` (in SG1-B) | none | **Records**: recount the 7 at the Lean tip; move `Call`/`Clean` to the scheduled reader PR |
| **FE-LIVE-1** · `clA5Compare_compute` | 1 (113+6) | 1 (`clA5EqNum_native`) | 0 | — | 0 (gate 121 sealed it) | none | none | **Close in records**: already converted (`Hardness:7252` cites `exists_first_entry_of_fixed`) |
| **Total if A + B run, C/UH/item 13 carried** | | ≈5 touched proofs + new ones | **est. −230 to −30** | ≈21 / 0–5 | ≈7 moved + ≈5 use sites | 2 modules, ≈14 public decls + equations | none public | 2 Lean PRs + records |

**Bottom line.** Of the families, only kind 4 (with its one-sided riders) and PL-1 are clear line
wins. Kinds 1, 2 and 5 are roughly line-neutral but retire 12 exact pairs and 368 duplicated
lines, which justifies a run with a stop rule. Kinds 3 and 6 publish a *host*, and policy then
requires a time and envelope contract that does not exist today. Without that clause they are a
coin flip; with it they are a loss. SG1-UH and item 13 are not copy debt: running them costs more
than it saves, as R2c did. FE-LIVE-1's front and FH-1's in-file copies are already retired in the
Lean, so the records are stale.

---

## 2. Findings that shape every family

1. **SG1 is not R2c.** In R2c three *frozen public* machines had to stay byte-identical, so each
   needed transport and instance code to reach the generic scanner. Here all members are
   `private`, and exact prefix-renaming twins (§3.1). The copies are deleted outright, with no
   transport. The "instance" code (each file's module bank, routing table and loop index) already
   exists. The cost drivers are different: rule 10, and the obligation that definitions land with
   their lemmas.
2. **Moving a definition creates foreign reads in unchanged proofs.** Hardness's use sites read
   the members' *bodies*. `clA5Copy_clean` runs `change … (false, (0 : Fin 3)) …` (the stop
   adapter's `q₀`) and `simpa only [clA5StopTM, Cfg.ofWords]`. `clA5Modules_bound` and
   `clA5Startup` run `simp [clA5StopTM, …]` (the adapter's `k`). `satReduction_poly` closes
   `hret0`–`hret5` (`satHostRet M i = …`) by `rfl` and reads the host's `k` and anchor transition by
   `change`. Once these definitions live in another module, each of those reads is a rule-10 read.
   A private `abbrev` alias does not help: TEMPLATE reports an abbreviation passed to `simp` where
   a published lemma exists, and the definitional reads still reach the foreign body. So the new
   API must publish readers (simps projections, `bankRet` case lemmas, an anchor-step lemma, an
   `initCfg` lemma), and those use sites are touched. Aliases are safe only for **lemmas**, whose
   consumers read statements only. That is the R1a precedent (#329, gate 143).
3. **The families depend on each other.** K1 needs K2, K5 and the FH twin. K6 needs K3 and K1. UH
   is built on item 13 (`clKeepLastPlacement`, `clPlacedAction/Cfg/_apply/_run`). FE-LIVE-1's
   residue reads item 13 (`clPlacedCfg_eq`, through `clPreparedCfg`). So item 13 and UH go
   together (both carried), K1 must not run after K6, and K3 goes with K6.
4. **The records are stale in three places.** The plan's R4 row lists
   - `clA5Compare_compute` as a held gate-121 front. It is converted: it cites
     `exists_first_entry_of_fixed` at `Hardness:7252`, gate 121 r2 records it as sealed, and no
     `Nat.find` remains in either file.
   - "FH-1's held implementations" under R4. All seven are outside SAT/Hardness (gate 122 r2:
     `Call`, `Clean`, `MARMTime`, `NDClockHostRun`, `clockStageCfg_captures`, two in
     `SingleTape`).
   - "22 exact pairs, 298 lines per file". Today there are 20 exact pairs plus 2 one-sided SAT
     residues: Hardness's `clA5_pt_tail/_head` now cite `polyTimeComputable_tail/_take1`. The 298
     reproduces exactly on the SAT side: K1–K5 including `sat_pt_tail/head` give 63+60+58+97+20.
5. **Further twins and instances are outside the 22.** My twin search found exact pairs the
   22-pair count leaves out: `sat_guard_add`/`clA5_guard_add` (`SAT:4035`/`Hardness:6368`, 16+2
   each; the inventory does not list it), `sat_live_prefix`/`clA5_live_prefix` (5+2) and
   `sat_call_first_halt`/`clA5_call_first_halt` (13+3). The two dispatchers differ only in
   `Fin 6`/`Fin 5`, the routing table and the loop-back entry (`satHostEntry M 2` vs `… 3`). Two
   one-sided kind-4 instances exist: `clFillTM/clFill_run/clNative_fill` (in the records) and
   `satScanTM/Cfg/_step/_run/_computes` (`SAT:230–301`, 60+10 lines; **not in the records or the
   inventory**). The near-twin search also pairs `sat_pt_pair/append/mapSnd/cond/and/linear` with
   `clNative_*`/`clA5_pt_*`. Those are gate 106's one-line citations of `PolyTimePairing`, not
   copies; leave them.

---

## 3. SG1 kinds 1–6

### 3.1 Members (all `private`, all in `namespace Complexity`; checked present)

"Exact" means byte-identical after comment stripping and replacing the prefixes
`sat`/`Sat` ↔ `clA5`/`CLA5`.

| Kind | SAT member | line | code+doc | Hardness member | line | code+doc | Relation |
|---|---|---|---|---|---|---|---|
| K1 | `SatClean` | 4054 | 5+2 | `CLA5Clean` | 6387 | 5+2 | exact |
| K1 | `satClean_stop` | 4063 | 16+3 | `clA5Clean_stop` | 6396 | 16+3 | exact |
| K1 | `satClean_install` | 4103 | 18+2 | `clA5Clean_install` | 6436 | 18+2 | exact |
| K1 | `satClean_emit` | 4124 | 15+2 | `clA5Clean_emit` | 6457 | 15+2 | exact |
| K2 | `satStopTM` | 3869 | 7+2 | `clA5StopTM` | 6203 | 7+2 | exact |
| K2 | `satStopCfg` | 3878 | 3+1 | `clA5StopCfg` | 6212 | 3+1 | exact |
| K2 | `satStop_step` | 3884 | 12+2 | `clA5Stop_step` | 6218 | 12+2 | exact |
| K2 | `satStop_clean` | 3909 | 29+4 | `clA5Stop_clean` | 6243 | 29+4 | exact |
| K3 | `satPadAction` | 3804 | 3+1 | `clA5PadAction` | 6138 | 3+1 | exact |
| K3 | `satPadTM` | 3809 | 6+1 | `clA5PadTM` | 6143 | 6+1 | exact |
| K3 | `satPadCfg` | 3817 | 5+1 | `clA5PadCfg` | 6151 | 5+1 | exact |
| K3 | `satPad_apply` | 3826 | 8+3 | `clA5Pad_apply` | 6160 | 8+3 | exact |
| K3 | `satPad_run` | 3836 | 16+1 | `clA5Pad_run` | 6170 | 16+1 | exact |
| K3 | `satPad_seam` | 3854 | 12+1 | `clA5Pad_seam` | 6188 | 12+1 | exact |
| K4 | `satMapWord` | 2745 | 4+2 | `clA5MapWord` | 6647 | 4+2 | exact |
| K4 | `satMapTM` | 2752 | 10+2 | `clA5MapTM` | 6654 | 10+2 | exact |
| K4 | `satMapCfg` | 2764 | 3+1 | `clA5MapCfg` | 6666 | 3+1 | exact |
| K4 | `satMap_run` | 2772 | 34+4 | `clA5Map_run` | 6674 | 34+4 | exact |
| K4 | `satMap_poly` | 2808 | 10+1 | `clA5Map_poly` | 6710 | 10+1 | exact |
| K4 | `sat_pt_tail` | 2824 | 12+1 | `clA5_pt_tail` | 6722 | 4+1 | one-sided: Hardness cites `polyTimeComputable_tail` |
| K4 | `sat_pt_head` | 2838 | 12+1 | `clA5_pt_head` | 6728 | 2+1 | one-sided: Hardness cites `polyTimeComputable_take1` |
| K5 | `sat_bridge_bound` | 4083 | 17+3 | `clA5_bridge_bound` | 6416 | 17+3 | exact |
| K6 | `SatHostState` | 3941 | 1+2 | `CLA5HostState` | 6275 | 1+2 | exact up to `Fin 6`/`Fin 5` |
| K6 | `satHostEntry` | 3950 | 2+1 | `clA5HostEntry` | 6283 | 2+1 | exact up to `Fin 6`/`Fin 5` |
| K6 | `satHostRet` | 3954 | 4+1 | `clA5HostRet` | 6287 | 4+1 | exact up to `Fin 6`/`Fin 5` (reads its own `…HostNext`) |
| K6 | `satHostTM` | 3962 | 9+3 | `clA5HostTM` | 6295 | 9+3 | loop-back entry `2` vs `3` |
| K6 | `satHost_seam` | 3975 | 12+3 | `clA5Host_seam` | 6308 | 12+3 | exact up to `Fin 6`/`Fin 5` |
| K6 | `satHost_call` | 3992 | 40+4 | `clA5Host_call` | 6325 | 40+4 | exact up to `Fin 6`/`Fin 5` |
| K6 | `satHost_clean` | 4154 | 13+1 | `clA5Host_clean` | 6474 | 13+1 | exact up to `Fin 6`/`Fin 5` |
| rider | `sat_live_prefix` | 3899 | 5+2 | `clA5_live_prefix` | 6233 | 5+2 | exact; one-line citation of `runFrom_state_ne_none_of_le` |
| rider | `sat_guard_add` | 4035 | 16+2 | `clA5_guard_add` | 6368 | 16+2 | exact (via `Turing.Segment.trans`) |
| rider | `sat_call_first_halt` | 3749 | 13+3 | `clA5_call_first_halt` | 6123 | 13+3 | exact (via `exists_first_halt`) |

Client data that stays: `satHostNext` (`SAT:3945`, 3+2) and `clA5HostNext` (`Hardness:6279`, 2+2).
One-sided kind-4 riders: `satScanTM` 230 (9+2), `satScanCfg` 241 (3+1), `satScan_step` 246 (14+1),
`satScan_run` 266 (24+5), `satScan_computes` 292 (10+1), and `clFillTM` 667 (8+2), `clFill_run`
678 (32+2), `clNative_fill` 713 (13+2).

**Totals per side, measured.** K1 63, K2 60, K3 58, K4 (exact part) 71, K5 20, K6 96, riders 41.
That is **409 lines a side, 818 in all**. The exact K1–K5 part is 272 lines a side; 298 with the
two SAT head/tail residues. The one-sided riders add 155 lines (26 + 70 + 59).

### 3.2 Proposal

Two new modules. They group the code by layer: hosts and machine adapters go in `Build`, and
polynomial-time corollaries in `ClassNP`. Their imports are modules `SAT` already reaches today
(the definers of `stateWord`, `Cfg.ofWords`, `emitAction`/`emitCfg`/`emit_run`,
`FinTM.controlAction`, `Turing.Segment`, `FinTM.exists_installCallTM`/`exists_emitCallTM`,
`PolyTimeComputable`, `FinTM.inputSymbol_at`). Their exact module names must be read off the tree;
they are not in the bundle. Neither new module may import `SAT`. **`SAT` gains one or two
imports. That is a new import into a frozen file, flagged for Seyoon.** `Hardness` reaches the new
modules through `SAT` and needs no new import.

- **M-T** `TCSlib/Complexity/ClassNP/OneWayTransducer.lean` (SG1-A). It could instead go into the
  colleague-owned `ClassNP/Transducer.lean` if that file's transducer gained a final emission.
  That would be a colleague interface change, so the new module is the default.
- **M-C** `TCSlib/Complexity/TuringMachine/Build/CleanCall.lean` (SG1-B, and SG1-C if run), with
  its polynomial-time corollaries in `ClassNP/CleanCallPoly.lean`. Alternatively, put the two
  corollaries beside `FinTM.exists_installCallTM`/`exists_emitCallTM`, of which they are direct
  consequences; that saves one module header (about 25–35 lines).

The proposed statements below are uncompiled. Names are proposals for Seyoon. Docstrings follow
`policy.md` §2–3: these are construction glue with no textbook counterpart, so they carry no
declaration-level tag. Each module's `## References` cites [AB09, §1.2] for the multitape model.

**SG1-A (M-T, namespace `Complexity`).**

```lean
/-- The word computed by a finite one-way transducer with state set `S`: on input bit `b` in
state `q` it emits `emit q b` (at most one bit) and moves to `next q b`; at the right end it
emits `finish q`. -/
def oneWayWord {S : Type} (next : S → Bool → S) (emit : S → Bool → Option Bool)
    (finish : S → Option Bool) : S → List Bool → List Bool
  | q, [] => (finish q).toList
  | q, b :: r => (emit q b).toList ++ oneWayWord next emit finish (next q b) r

/-- `oneWayWord` on the empty word is the final emission. -/
theorem oneWayWord_nil … : oneWayWord next emit finish q [] = (finish q).toList
/-- `oneWayWord` on `b :: r` emits `emit q b` and continues from `next q b`. -/
theorem oneWayWord_cons … : oneWayWord next emit finish q (b :: r) =
    (emit q b).toList ++ oneWayWord next emit finish (next q b) r

/-- The zero-work-tape machine realizing `oneWayWord … start`: one right move per input bit,
then one halting transition at the right blank. -/
@[simps (config := { isSimp := false })]
def oneWayTM {S : Type} [Fintype S] [DecidableEq S] (next : S → Bool → S)
    (emit : S → Bool → Option Bool) (finish : S → Option Bool) (start : S) : FinTM Bool

/-- `oneWayTM` computes `oneWayWord … start` in time `n + 1`.
**Proof sketch.** Induct on the unread suffix. Each input bit is one transition that appends
its optional emission, and the right blank is the final halting transition. -/
theorem oneWayTM_computesFunInTime … :
    (oneWayTM next emit finish start).ComputesFunInTime
      (oneWayWord next emit finish start) (fun n => n + 1)

/-- Every finite one-way transduction is polynomial-time computable. -/
theorem polyTimeComputable_oneWayWord … : PolyTimeComputable (oneWayWord next emit finish start)
```

`…MapCfg` and the run induction become `private` inside M-T. All ten twins are deleted. The
riders become citations and keep their names, so their use sites stay byte-identical:
- `satScanTM` becomes a private abbreviation of `oneWayTM step (fun _ _ => none) (some ∘ accept)`.
  `satScan_computes` follows from `oneWayTM_computesFunInTime` and the identity
  `oneWayWord step (fun _ _ => none) (some ∘ accept) q x = [accept (x.foldl step q)]` (est. 6–10
  lines). `satScanCfg`, `satScan_step` and `satScan_run` are deleted.
- `clNative_fill` is re-proved through `polyTimeComputable_oneWayWord` at constant emission;
  `clFillTM` and `clFill_run` are deleted.
- `sat_pt_tail`/`_head` cite `polyTimeComputable_tail`/`_take1`, as Hardness already does. This
  needs `SAT` to import `ClassNP/PolyTimeBlockLoop`, a decision the backlog lists as pending.
  Without that import they stay, retargeted to `oneWayWord_*`.

**SG1-B (M-C, namespace `Turing.FinTM`; corollaries in `Complexity`).**

```lean
/-- `M` is a clean module for `result`, `emit` and budget `B`: it has a work tape, and from
every untouched native input `x` and argument `arg` stored as the canonical state word, it
first halts at a positive time `t ≤ B |arg|`. It leaves the state word `result arg` with every
head at the origin and has emitted exactly `emit arg`. -/
structure CleanModule (M : FinTM Bool) (result emit : List Bool → List Bool) (B : ℕ → ℕ) :
    Prop where
  pos : 0 < M.k
  run : ∀ x arg : List Bool, ∃ t, 0 < t ∧ t ≤ B arg.length ∧
    (∀ v < t, ¬(M.tm.runFrom (Cfg.ofWords (input := x) M.tm.q₀ (stateWord M.k arg)) v).Halted) ∧
    M.tm.runFrom (Cfg.ofWords (input := x) M.tm.q₀ (stateWord M.k arg)) t =
      {Cfg.ofWords M.tm.q₀ (stateWord M.k (result arg)) with state := none, output := emit arg}

/-- Release-flag stop adapter: runs `C` from `entry`, and halts silently on the first visit to
`exit` made after at least one step (so `entry = exit` is allowed). -/
@[simps (config := { isSimp := false })]
def stopTM (C : FinTM Bool) (entry exit : C.State) : FinTM Bool
/-- The adapter's configuration: `c` with release flag `b` paired onto its state. -/
@[simps (config := { isSimp := false })]
def stopCfg {k : ℕ} {S : Type} {x : List Bool} (b : Bool) (c : Cfg k Bool S x) :
    Cfg k Bool (Bool × S) x
/-- Before the designated exit, the adapter takes the module's physical step and raises the
release flag. -/
theorem stopTM_step … : (stopTM C entry exit).tm.step (stopCfg b c) = stopCfg true (C.tm.step c)
/-- A positive return to `exit` with the guard becomes a silent halt one step later, keeping
every seam field and the emitted output.
**Proof sketch.** Induct on prefixes. The flag is false only at time zero, the guard prevents an
early stop, and the final transition is silent. -/
theorem stopTM_runFrom_clean … : (stopTM C entry exit).tm.runFrom
    (Cfg.ofWords (input := x) (false, entry) (stateWord C.k arg)) (t + 1) =
    {Cfg.ofWords (true, exit) (stateWord C.k result) with state := none, output := out}
/-- A guarded positive-return bridge contract makes `stopTM` a clean module with budget
`B + 1`. -/
theorem CleanModule.of_stop … : CleanModule (stopTM C entry exit) result emit (fun n => B n + 1)

/-- A run that starts live and halts by time `t` has a positive first halt `u ≤ t` with the same
endpoint. -/
theorem _root_.Turing.MultiTapeTM.exists_first_halt_pos … : ∃ u, 0 < u ∧ u ≤ t ∧
    (∀ v < u, ¬(tm.runFrom cfg v).Halted) ∧ tm.runFrom cfg u = tm.runFrom cfg t
/-- Two consecutive segments that both avoid `anchor`, with the seam also off it, avoid `anchor`
throughout (a corollary of `Turing.Segment.trans`). -/
theorem _root_.Turing.MultiTapeTM.avoid_add … : ∀ v < a + b, (tm.runFrom c v).state ≠ some anchor

-- ClassNP/CleanCallPoly.lean, namespace Complexity
/-- Every polynomial-time `f` has a clean install module (result `f`, no output) with a
polynomial budget in the argument length. -/
theorem exists_cleanInstall {f} (hf : PolyTimeComputable f) :
    ∃ M A d, FinTM.CleanModule M f (fun _ => []) (fun n => A * (n + 1) ^ d)
/-- Every polynomial-time `f` has a clean emit module (argument kept, output `f`) with a
polynomial budget. -/
theorem exists_cleanEmit {f} (hf : PolyTimeComputable f) :
    ∃ M A d, FinTM.CleanModule M id f (fun n => A * (n + 1) ^ d)
```

K5's `bridge_bound` becomes `private` in `CleanCallPoly`, its only consumer, so it adds no new
public API. The SG1 ledger's own kind-5 proposal (a public arithmetic lemma) is not needed.
`sat_live_prefix`/`clA5_live_prefix` are deleted, and `stopTM_runFrom_clean` cites
`runFrom_state_ne_none_of_le` directly. `exists_first_halt_pos`'s natural home is beside
`exists_first_halt` in `Finite`, but that file sits low in the import graph and adding to it
replays most of the library. So M-C is proposed, with `Finite` as Seyoon's alternative.

In the files, `SatClean`/`CLA5Clean` stay as one-line private `abbrev`s of `FinTM.CleanModule`, so
private headers stay byte-identical. Reading an abbreviation is allowed, and consumers use only
`h.1`/`h.2`, which are now structure projections. `satClean_install/_emit` and
`clA5Clean_install/_emit` stay as private citations of `exists_cleanInstall/_cleanEmit`, header
kept (R1a precedent), and so do `sat_guard_add`/`clA5_guard_add`. The large consumers
`satReduction_poly`, `clA5Round` and `clA5Output_of_nativeChunk` are then **not touched** by SG1-B.
`clA5StopTM` cannot be aliased (finding 2): its four readers are repaired through `stopTM_k`,
`stopTM_tm_q₀` and `stopTM_State`.

**SG1-C (M-C, only if run).** These are the same SAT declarations, generalized:

```lean
/-- State of the shared-bank dispatcher over a finite family of modules: the anchor, or a
module index with that module's state. -/
abbrev BankState {n : ℕ} (M : Fin n → FinTM Bool) := Unit ⊕ (Σ i, (M i).State)
theorem bankState_eq … -- abbrev lemma (TEMPLATE: new public abbrev lands with its lemma)
/-- Entry state of module `i`. -/
def bankEntry (M : Fin n → FinTM Bool) (i : Fin n) : BankState M
/-- Where module `i` returns: the entry of `next i`, or the anchor when `next i = none`. -/
def bankRet (next : Fin n → Option (Fin n)) (M) (i) : BankState M
theorem bankRet_of_some … ; theorem bankRet_of_none …
/-- Bank padding: a `k`-tape action or configuration on `K ≥ k` tapes, extra tapes blank and
stationary. -/
@[simps …] def bankPadAction … ; @[simps …] def bankPadTM … ; @[simps …] def bankPadCfg …
theorem bankPadAction_apply … ; theorem bankPadTM_runFrom … ; theorem bankPadCfg_ofWords …
/-- The finite-family dispatcher: padded modules share one `K`-tape bank; module `i` returns to
`bankRet next M i`, and the anchor dispatches to `bankEntry M loop`. -/
@[simps (config := { isSimp := false })]
def bankHostTM (M : Fin n → FinTM Bool) (next : Fin n → Option (Fin n)) (start loop : Fin n)
    (K : ℕ) (hk : ∀ i, (M i).k ≤ K) : FinTM Bool
theorem bankHostTM_initCfg … : (bankHostTM M next start loop K hk).tm.initCfg x =
    Cfg.ofWords (bankEntry M start) (stateWord K [])            -- replaces two `hi` blocks
theorem bankHostTM_step_anchor … : (bankHostTM …).tm.step
    {Cfg.ofWords (input := x) (.inl ()) (stateWord K w) with output := out} =
    {Cfg.ofWords (bankEntry M loop) (stateWord K w) with output := out}  -- replaces two `dispatch`
theorem bankHost_seam … ; theorem bankHost_call … ; theorem bankHost_clean …
```

**Policy gate.** `bankHostTM` is a dispatcher, so it is a *host* under policy §1 ("Hosts come
first"). Its public contract must carry time *and* space (head-envelope) clauses and be registered
in `machine-library-design.md` §14. `CleanModule` has no space clause, and neither do
`exists_installCallTM`/`exists_emitCallTM` as consumed here. So an envelope clause means
extending the contract and every module's proof: est. +100 to +300 lines. The consumers are
polynomial-time reductions and need no space bound. A time-only contract, with the envelope
deferred and recorded, is Seyoon's call.

**Other K3 candidates, not drop-ins.**
- `Turing.embedEmitTM` at `Fin.castLEEmb` (the inventory's suggestion). R1's transition selects
  slots through a `List.finRange … find?` lookup: `clPlacedAction_eq` (`Hardness:1915`) unfolds it
  by `change`, and item 13's `clPlacement_lookup` exists to close it. Padding through R1 would need
  a published lookup equation at `castLEEmb` or item 13's selector layer.
- `Build/EmitIterEmbed`'s public `padAction`/`embedCfg`/`embed_run` layer (ledger L311). Its
  statements are not bundled. Compare it before choosing K3's home. The `bankPad*` names above
  avoid colliding with it.

### 3.3 Use sites (every declaration whose text mentions a member; measured)

| Use site | file:line | lines | via | Touched by |
|---|---|---|---|---|
| `satEval_start`, `satPair_start` | SAT:701, 2549 | 47, 38 | `sat_first_halt` (not a twin, kept) | — |
| `satReq_fields_poly`, `satReqLink_poly`, `satReqEmit_poly`, `satReqStep_poly` | SAT:3537, 3565, 3580, 3593 | 21, 3, 10, 15 | `sat_pt_head/tail` (names kept) | — |
| `satSyntax_poly`, `satWidthScan_poly` | SAT:305, 1041 | 4, 4 | `satScanTM`, `satScan_computes` (names kept) | — |
| `satAppend_clean` | SAT:3767 | 35 | `sat_call_first_halt` | B |
| `satReduction_poly` | SAT:4176 | 158 | install/emit, `satHost*`, `sat_guard_add` | C (B only if aliases dropped) |
| 9 users of `clNative_fill` (`clPrepHeader_native` … `clA5Fragment_native`) | Hardness:750–7992 | 111 | name kept | — |
| `clA5Copy_clean` | Hardness:6492 | 32 | `clA5StopTM`, `clA5Stop_clean`, `clA5_call_first_halt` | B |
| `clA5Packed_install`, `clA5Cursor_install` | Hardness:6528, 6541 | 5, 3 | `CLA5Clean`, install (aliased) | — |
| `clA5Modules` | Hardness:6547 | 7 | `clA5StopTM` (in a def body) | B (rename) |
| `clA5Modules_bound` | Hardness:6556 | 4 | `simp [clA5StopTM]` | B |
| `clA5Startup` | Hardness:6570 | 55 | `clA5StopTM`, `clA5Host*`, `clA5_guard_add` | B, C |
| `clA5Round` | Hardness:7028 | 38 | `CLA5Clean`, `clA5Host*`, `clA5_guard_add` | C |
| `clA5Output_of_nativeChunk` | Hardness:7123 | 72 | install/emit, `clA5HostTM` | C |
| `clA5Div_native` | Hardness:7726 | 27 | `clA5MapWord`, `clA5Map_poly` | A |
| `clA5GetBit_native` | Hardness:7877 | 12 | `clA5_pt_head` (kept) | — |

Eighteen declarations mention a SG1 member, plus the 9 `clNative_fill` users and 2 `satScan` users.
With names kept as above, **9 are touched**: A touches 1, B touches 4 plus `clA5Modules`, and C
touches 4.

### 3.4 Net cost (removed measured, added estimated)

| | A (kind 4 + riders) | B (kinds 1, 2, 5 + riders) | C (kinds 3, 6) |
|---|---|---|---|
| Removed, both files | 142 (+ riders: `satScan` 70, `clFill` 59, head/tail 26) | 368 | 308 |
| Shared copy moved into the new module | 71 | 177 (`live_prefix` deleted) | 154 |
| Generalization (`Fin n`, `next`, `start`, `loop`) | — | — | 4–8 |
| Equations and readers (simps, `_nil/_cons`, `bankRet_*`, anchor, `initCfg`) | 6–12 | 3–8 | 26–40 |
| Public docstrings (statement prose, sketches) | 6–12 | 15–35 | 15–30 |
| Module header and docstring | 25–35 | 50–70 (2 modules) | 0 (shares M-C) |
| Rule-10 repairs inside moved proofs | 4–15 | 8–30 | 10–35 |
| New equations in other owners' files (§3.5) | 0–8 | 0–15 | 8–25 |
| Aliases and citations kept in SAT/Hardness | rider citations: `satScan` 18–25, `clNative_fill` 14–24, head/tail 8 | 30–42 | 0 |
| Use-site edits and repairs | 0–5 | 10–40 | −16 + 15–60 |
| **Net** | **−150 to −80** (core alone −30 to +15) | **−80 to +50** | **−90 to +35** (time-only); +10 to +335 with envelope |

**Pairs.** A retires 5 exact pairs, the 2 one-sided head/tail residues (if the import is approved)
and 2 one-sided instances (`satScan*`, `clFill*`). B retires 12: K1 4, K2 4, K5 1, and the
`live_prefix`, `guard_add` and FH twins. C retires 13: K3 6, K6 7. **Created: est. 0–4 overall.**
There is no per-instance adapter layer to resemble itself, as R2c's did. The risks are the short
citation aliases if the screen does not exclude one-liners, and the two word identities
(`satScan`, `clFill`). The similarity between `satReduction_poly`'s startup and round and
`clA5Startup`/`clA5Round` already exists and is not changed; a generic "round of clean calls"
lemma would be a later, separate API.

### 3.5 Rule-10 exposure (read forms in the proof text today; measured)

A row marked *moved* is a SAT member that becomes the shared copy; its Hardness twin is deleted
and needs no repair. Readers marked ✓ are evidenced in the bundle, because a bundled proof cites
them.

| Declaration | Group | Reads of other files' definitions today | Repair |
|---|---|---|---|
| `satMap_run` (moved) | A | `unfold MultiTapeTM.step`; `change` on `tr`; `simp [MultiTapeTM.step, Cfg.inputSymbol, Action.apply]` | `MultiTapeTM.step_of_some`/`step_of_halt` ✓, `FinTM.inputSymbol_at` ✓, `Action.apply_*` ✓ |
| `satMap_poly` (moved) | A | anonymous constructor of `PolyTimeComputable`; `Cfg.ext_zero_tapes rfl rfl rfl` against `initCfg` | `MultiTapeTM.initCfg_eq` ✓; **`PolyTimeComputable` intro: not evidenced, new if absent** |
| `clA5Div_native` | A | `rw`/`simp [clA5MapWord]` (becomes foreign) | `oneWayWord_nil/_cons` (own API) |
| `satStop_step` (moved) | B | `simp only [MultiTapeTM.step, …]`, closing `rfl` | `step_of_some` ✓ |
| `satStop_clean` (moved) | B | `simp [MultiTapeTM.step, Cfg.ofWords, FinTM.controlAction, Action.apply]`; `zero => rfl` reads `runFrom`; `hi : … := rfl` reads `Cfg.ofWords` | `step_of_some` ✓, `runFrom_zero` ✓, `Cfg.ofWords_*` ✓, `controlAction_apply` ✓, `Action.apply_*` ✓ |
| `satClean_stop` (moved) | B | `simp [Cfg.ofWords]`, `simpa only [Cfg.ofWords]` | `Cfg.ofWords_state` ✓ (and the other `Cfg.ofWords_*`) |
| `satClean_install/_emit` (moved) | B | `obtain ⟨F, A, d, hF⟩ := hf` destructures `PolyTimeComputable` | **`PolyTimeComputable` elim: not evidenced, new if absent** |
| `satAppend_clean` | B | `simp [Cfg.ofWords]`; `Cfg.ext rfl rfl ?_ rfl rfl` and `fin_cases … rfl` reading `Cfg.ofWords`/`stateWord` (13 `rfl`) | `Cfg.ofWords_*` ✓; **`stateWord` equation: not evidenced** |
| `clA5Copy_clean` | B | `simp [MultiTapeTM.initCfg, Cfg.init, Cfg.ofWords, stateWord, FinTM.bufferTape]`; 2 `change` reading the stop adapter's `q₀`; `simpa only [clA5StopTM, Cfg.ofWords]` | `initCfg_eq` ✓, `bufferTape_*` ✓, `stopTM_tm_q₀` (own simps), **`stateWord`** |
| `clA5Modules_bound` | B | `simp [clA5StopTM]` for `.k` | `stopTM_k` (own simps) |
| `clA5Startup` | B, C | the `initCfg` block above; `simp [clA5StopTM]`; 3 `change` reading host `k`/entry/ret; closing `rfl` | `stopTM_k`, `bankHostTM_initCfg`, `bankHostTM_k`, `bankRet_*` (own) |
| `satPad_apply` (moved) | C | `simp [Action.apply]` | `Action.apply_*` ✓ |
| `satPad_run` (moved) | C | `simp [MultiTapeTM.step]` (twice), `change`, `simp [Cfg.workTapeSymbols]` | `step_of_some`/`step_of_halt` ✓, `Cfg.workTapeSymbols_eq` ✓ |
| `satPad_seam` (moved) | C | `simp [Cfg.ofWords, stateWord, FinTM.bufferTape]` | `Cfg.ofWords_*` ✓, `bufferTape_nat/left` ✓, **`stateWord`** |
| `satHost_seam` (moved) | C | `Cfg.ext rfl rfl ?_ ?_ rfl` reads `emitCfg`/`Cfg.ofWords` fields | **`emitCfg` field equations: not evidenced** |
| `satHost_call` (moved) | C | `simp [emitCfg, …]`; `by intros; rfl` (reads only same-module defs after the move) | **`emitCfg` field equations** |
| `satReduction_poly` | C | `initCfg`/`Cfg.init`/`Cfg.ofWords`/`stateWord`/`bufferTape` block; `hdispatch` (`change` + `simp [FinTM.controlAction, Action.apply, Cfg.ofWords]`); `simp [pairEncode, …]` (`hpa`); `hret0–5 := rfl`; 9 `change`, 15 `rfl` | readers above; **`pairEncode` append equation: not evidenced** |
| `clA5Round` | C | `dispatch` block (as above); 5 `change`; closing `rfl` | `bankHostTM_step_anchor`, `bankRet_*` |
| `clA5Output_of_nativeChunk` | C | rename only; its `change`s read local `let`s | none expected |

No read: `sat_bridge_bound` (pure `Nat`), `sat_guard_add` (`Turing.segment_iff` ✓),
`sat_call_first_halt` (`runFrom_zero` ✓), `satHost_clean` and `SatClean` (same-module
projections), `sat_live_prefix`.

**Totals.** A: 2 moved proofs and 1 use site. B: 5 moved proofs and 4 use sites. C: 5 moved
proofs and 4 use sites, `clA5Startup` counted once. Published equations that may be needed in
other owners' files, all to be checked in the tree first:
- `stateWord`: one or two equations
- `emitCfg`: up to five field equations
- `PolyTimeComputable`: introduction and elimination
- `pairEncode`: one append identity

My parser cannot see anonymous-constructor reads or `exact` steps that unify through a body; the
seals remain the authority (§10).

### 3.6 Statement changes

None public. Both files' public declarations (`SAT`, `SAT3`, `SAT_mem_NP`,
`SAT_exists_linear_verifier`, `SAT3_mem_NP`, `SAT_reducible_SAT3`; `NPHard.polyTimeReducible`,
`SAT_NPHard`, `SAT_NPComplete`, `SAT3_NPHard`, `SAT3_NPComplete`) mention no member. Private
statements: none change under A or B with the aliases above. Under C, `clA5Startup` and `clA5Round`
bind `let H := bankHostTM …` and change privately.

### 3.7 Recommendation and slicing

- **R4-1 (pilot): run.** SG1-A plus PL-1. It has the smallest exposure
  (3 proofs) and the clearest saving. Measure its net lines and copy-screen pairs against this
  note before R4-2.
- **R4-2: run, with a stop rule.** SG1-B, after Seyoon approves the §3.2 API (the standing rule:
  the 2026-11-07 ruling authorizes retained debt, not a new API). Stop and carry B in the
  register if, before merge, the measured net exceeds **+50 lines** or the screen shows more pairs
  created than retired.
- **R4-3: carry by default.** SG1-C. Run it only if Seyoon accepts a time-only host contract
  (§3.2 policy gate), and only after R4-2's measurement. If carried, the register entry is
  "K3 + K6, 13 pairs, 308 lines, both files; carried because a public host needs an envelope
  contract the consumers do not use". The private K6 copies then state `…Host_clean` against
  `FinTM.CleanModule` through the alias.
- Each PR edits `SAT` and `Hardness`, so each replays `SAT`'s downstream closure; that closure is
  not measurable from the bundle. With R4-3 carried, there are 2 Lean PRs instead of the plan's
  4–6.

---

## 4. SG1-UH: the unary-clock host

**Members (measured, `Hardness`, all private; 4 definitions and 10 lemmas):**
- `clRepeatTM` 5656 (16+2), `clRepeatCfg` 5675 (7+2), `clRepeat_frame` 5684 (13+1)
- `clRepeat_call` 5704 (45+6), `clRepeat_round` 5753 (27+3), `clRepeat_complete` 5787 (31+6)
- `clRepeatWords` 5821 (2+2), `clRepeat_initial` 5825 (8+1), `clRepeatOutputTM` 5835 (3+1)
- `clRepeatOutput_compute` 5845 (41+6), `clRepeat_budget` 5961 (33+3)
- `clRepeatArgument_native` 5997 (16+2), `clA5Iter_native` 6747 (32+6),
  `clA5Iter_shrinking` 6782 (19+2)

That is 293+43 = 336 lines, with no SAT twin. **This is not copy debt.** It is a private host,
retained by Seyoon's 2026-11-07 ruling.

**Use sites:**
- **Outside the family:** `clVisitRows_native` 6040 (36), `clA5Field_native` 6841 (13),
  `clA5Decode_native` 7421 (26).
- **Inside:** the host is built on item 13: `clRepeatTM`, `clRepeat_frame`, `clRepeat_call` and
  `clRepeatOutput_compute` use `clKeepLastPlacement`, `clPlacedAction/Cfg`, `clPlaced_apply/_run`.
  It also builds on Hardness's private native loader and replay (`clPreparedTM`, `clPrepared_run`,
  `clPrepared_idle`, `clOutputTM`, `clOutputAt_compute`, `clFields`, `clNative_image`).

**Proposal if run.** Move the core host (`clRepeatTM`, `clRepeatCfg`, `_frame`, `_call`, `_round`,
`_complete`, `clRepeatWords`, `_initial`; 172 lines) into `Build` as a public unary-clock host. It
would be restated over R1 (`embedEmitTM` at `Fin.castAddEmb 1`) or over a published item-13
layout, with B1040's contract:

```lean
/-- Unary-clock repetition host: from a clean-call contract of `C` (positive first return from
`entry` to `exit`, all scratch restored), runs `C` once per occupied cell of a protected unary
clock tape and halts silently on the clock's blank. -/
def repeatTM (C : FinTM Bool) (entry exit : C.State) : FinTM Bool
/-- `N` bounded clean calls along the orbit of `f` complete in at most `N (B + 2) + 1` steps,
with the final state word `f^[N] s`; **every head stays within the source envelope plus the
clock tape `[0, N]`**.
**Proof sketch.** Induct on the executed clock prefix: each round is a tick, one relocated clean
call and a return dispatch. The envelope clause follows each call's envelope and the clock
head's monotone walk. -/
theorem repeatTM_complete …
```

The output, budget, argument and `clA5Iter_*` declarations stay in `Hardness` as the consumer
side.

**Net (est.).** Removed: at most 172 lines; the consumer half stays. Added:
- the moved 172
- re-expression without item 13: +20–60
- head-envelope and resource clauses, which are **new proofs** (no space fact exists today):
  +80–200
- docs, equations and module header: +70–110

That is **+170 to +370** net, with 0 pairs retired. Rule 10: the 14 members and 3 use sites read
`Cfg.ofWords`, `Cfg.workTapeSymbols`, `MultiTapeTM.step`, `Action.apply`, `stateWord`,
`seamCompTM` and `pairEncode` (by `simp`), plus `Fin.addCases` (a Mathlib definition passed to
`simp`). Their 23 `rfl`, 5 `change` and 8 `show` steps mostly read the clock configuration. Once
moved, every `clPlaced*`/`clKeepLastPlacement` read becomes foreign or must be rewritten.

**Statement changes:** none.

**Recommendation: carry** in the register as an accepted private host with one consumer.
Policy's harvest trigger is "before a second consumer is briefed", and none is.

**One lead could flip this.** If `ClassNP/PolyTimeBlockLoop` (or another public module) already
exports a polynomial *iteration closure*, then `clA5Iter_native` and `clA5Iter_shrinking` could
cite it. All 12 `clRepeat*` would become dead code, about −300 lines with no new API. That closure
would read: `PolyTimeComputable f`, `s`, and unary `N`, plus a polynomial orbit-size bound, imply
`PolyTimeComputable (fun x => f^[N x] (s x))`. The bundle only shows the `BlockLoop` orbit layer
(backlog BL-W), which looks ch7-specific. A one-line `git grep` settles it.

---

## 5. PL-1's twins

**Members (measured):** `sat_pt_eq` (`SAT:2853`, 7+2) and `clA5_pt_eq` (`Hardness:6733`, 7+2).
They are exact twins modulo their local linear-lift aliases `sat_pt_linear` (`SAT:79`) and
`clNative_linear` (`Hardness:628`), which are both one-line citations of
`polyTimeComputable_of_linear`. Each lifts `FinTM.computesFunInTime_ifEq w [true] [false]` and
converts it to `[decide (f x = w)]`. Also in the family: `a3n_poly_linear`/`a3n_poly_const` in
`ClassNP/Nondeterminism`, which is **not bundled**, so it is unverified here.

**Proposal.** Each body becomes the citation the ledger names, keeping names and headers:

```lean
private lemma sat_pt_eq {f : List Bool → List Bool} (hf : PolyTimeComputable f) (w : List Bool) :
    PolyTimeComputable (fun x => [decide (f x = w)]) := by
  simpa only [Function.comp_def] using
    (polyTimeComputable_of_linear (FinTM.computesFunInTime_decideEq w)).comp hf
```

`clA5_pt_eq` is identical. `a3n_poly_linear`/`_const` are re-pointed to
`polyTimeComputable_of_linear`/`_const`.

**Use sites (measured):**
- `satReqLink_poly` 3565, `satReqEmit_poly` 3580, `satReqStep_poly` 3593
- `clA5WorkFragment_native` 7694, `clA5Select_native` 7764, `clA5IfZero_native` 7869,
  `clA5GetBit_native` 7877

All stay byte-identical because the names are kept.

**Net:** est. −8 (9 → 5 lines each), plus −5 to −8 in `Nondeterminism` (unverified). Pairs: 1
retired, plus the `Nondeterminism`/`PolyTimePairing` pair; 0 created. **Rule 10:** the new bodies
read no definition (`Function.comp_def` is a lemma); no repairs.

**Imports:** `SAT` must reach `Build/WordTests`. Its direct imports do not include it, and its
transitive reach is not visible in the bundle; the inventory says it does not reach it. **Flag:**
a new import into `SAT` if needed. Hardness gets it through `SAT`.

**Statement changes:** none. **Recommendation: run**, riding R4-1.

---

## 6. 12.2c item 13: `clPlacement`

**Members (measured, `Hardness`, all private):**
- **Layer (17 declarations, 209+32):** `clPlacement` 1760 (structure); `.ofInverse` 1766,
  `.permute` 1777, `.refl` 1791, `.empty` 1797, `.sum` 1805, `.comp` 1839, `.trailing` 1854;
  `clKeepLastPlacement` 1872; `clPlacement_lookup` 1888; `clPlacedAction` 1903, `clPlacedCfg`
  1908; `clPlacedAction_eq` 1915, `clPlacedCfg_eq` 1930; `clPlaced_apply` 1964,
  `clPlaced_run` 1982, `clPlaced_release` 2545.
- **Selectors (9, 44+9):** `clRowSelect` 2000, `clRecTrackSelect` 2296, `clRecRowSelect` 2302,
  `clLoadSelect` 3474, `clPrepareSelect` 3820, `clRecordSelect` 4034, `clMatchLoadSelect` 4162,
  `clMatchCmpSelect` 4166, `clOneSelect` 4722.
- Two `attribute [local simp]` lines, at 1882 and 1958.

The ledger records this as "not copy debt … a private generic adapter" (ledger L40). It has no twin.

**What it is.** A certified selector over the public R1 transformer. `clPlacedAction`/`Cfg` are
`embedEmitTM`/`embedEmitCfg` followed by a state map. The selector `select : Fin l → Option (Fin k)`
is a *closed form of R1's own `find?` lookup*: `clPlacement_lookup` proves exactly that, and
`clPlacedAction_eq`/`clPlacedCfg_eq` turn R1's fields into `match slots.select j with …`, which the
42 consumers evaluate with `simp`/`fin_cases`.

**Use sites (measured):** 42 declarations, 1,112 lines (plus the 2 attribute lines). They are
every row, record, load, prepare, match, output, count and repeat machine with its frame and run
lemmas, from `clRowTM` 2015 to `clRepeatOutput_compute` 5845, plus `clA5Compare_compute` 7212.

**Proposal if run (MIG-21).** Plain `Fin k ↪ Fin l` embeddings (`Fin.castAddEmb`,
`Fin.natAddEmb`, `Function.Embedding.trans`, `Equiv.toEmbedding`) consumed through the
`embedEmit*` readers. At most one combinator (the sum of embeddings) would be promoted to
`Build/Embed`.

**Net (est.).** Removed: 296 lines. Added:
- 9 plain embeddings with injectivity proofs: 30–50
- per-layout range and preimage lemmas, since consumers still need "slot `j` is source `i`, or
  outside the range": 55–135
- consumer rewrites from `match select` to `embedEmitCfg_selected_*` and `embedEmitTM_frame` with
  range proofs: 0–125
- a sum-of-embeddings bridge: 10–30
- rule-10 repairs in 42 touched proofs: 40–170

That is **−160 to +215** net. Pairs: 0 retired. Created: the per-layout range lemmas would
resemble each other (0–9), the R2c pattern.

**Rule-10 exposure (measured over the 42):** 117 `rfl` and 21 `change`. Foreign `simp`/`unfold`
reads: `MultiTapeTM.step` (`clRec_copy`, `clRec_advance`, `clOutput_compute`,
`clOutputAt_compute`, `clPlaced_release`), `Cfg.mapState`, `Cfg.ofWords`, `MultiTapeTM.initCfg`,
`Cfg.init` (`clPrepare_start`), `FinTM.tapeBlocks`, `seamCompTM`, `stateWord`, and `Fin.addCases`
(a Mathlib definition passed to `simp`). Today the layer itself reads R1 by `change`
(`clPlacedAction_eq`, `clPlaced_apply`); `embedEmitTM_tr` (the item-6 export) would be the repair.

**Statement changes:** none (all private).

**Recommendation: carry**, recorded in the register as "private certified-layout adapter over R1;
no copy; dissolving it moves its `find?` closed form into 42 consumers". If Seyoon wants evidence,
run a one-layout pilot: `clRowSelect` with `clRowTM`, `clRow_frame` and `clRow_field`, 68 lines
today. Item 13 also gates UH (§4) and FE-LIVE-1's residue (§8).

---

## 7. FH-1's held implementations

**In the bundle:**
- `sat_first_halt` (`SAT:685`, 10+1) cites `exists_first_halt` (`SAT:691`); it is a thin
  specialization to `initCfg`/`ComputesInTime`. Keep it.
- `sat_call_first_halt`/`clA5_call_first_halt` cite `exists_first_halt` (`SAT:3754`,
  `Hardness:6128`) and are exact twins. They retire in SG1-B as
  `MultiTapeTM.exists_first_halt_pos` (§3.2). Their use sites are `satAppend_clean`,
  `satClean_stop`, `clA5Clean_stop` and `clA5Copy_clean`.

No `Nat.find` remains in either file.

**The seven held implementations (#242) are outside SAT/Hardness** (gate 122 r2):
- `Call.call_run` and `Clean.cleanTM_run`: ruled 2026-11-12 as open rule-10 fronts for a
  scheduled reader PR (readers for `SimRel`/`HaltRel` in `Machines/Sim`; `PB`, `markI`, `ccfg` in
  `Machines/CleanSweep`). The inventory says these are colleague-authored files.
- `MARMTime.runFrom_count_eq`, `NDClockHostRun.startup`, `clockStageCfg_captures`,
  `SingleTape.one_work_tape`, `SingleTape.dg_all_inputs`: rule-10 repairs landed in #242.

Whether those five now *cite* `exists_first_halt` cannot be decided from the bundle. The inventory
says yes; the ledger's 2026-11-16 closeout row says "held, and go to wave R4".

**Recommendation: records only.**
1. Grep the six owners at the Lean tip for `Nat.find` and `exists_first_halt`. Close each that
   cites the canonical lemma.
2. Move `call_run`/`cleanTM_run` from R4 to the scheduled reader PR. They are not SAT/Hardness
   work, and their interface design waits for the colleague.
3. Count the in-file twin in SG1-B.

---

## 8. FE-LIVE-1's Hardness front: `clA5Compare_compute`

**Member (measured):** `clA5Compare_compute` (`Hardness:7212`, 113+6). It selects the first
verdict with `MultiTapeTM.exists_first_entry_of_fixed` (`Hardness:7252`). It reads its
configurations through published equations: `MultiTapeTM.initCfg_eq`, `step_of_some`,
`Action.apply_*`, `Action.mapState_*`, `Cfg.workTapeSymbols_eq`, `Cfg.ofWords_workTapes`. Gate 121
r2 records it among the 24 proofs that pass whole-proof seals (commits `5abe015a`, `9936345a`).
Five more FE-LIVE-1 sites in Hardness already cite the canonical theorem (1279, 1742, 2164, 3003,
3271). Its only use site is `clA5EqNum_native` (7328).

**Proposal:** nothing to change. Net 0; no API; no statement change. **Recommendation: close in
the records.** The plan's R1 recount (2026-11-16) is stale on this point. Its remaining coupling
(`dsimp only [clPreparedCfg]; rw [clPlacedCfg_eq]`) is a same-file read that changes only if item
13 runs.

---

## 9. Cross-check against `maintainer-inventory-R4.json`

**Agreements, re-measured.** All **286** in-bundle entries (members and use sites with file, line
and span) match my parse exactly. These also agree:
- K1/K2/K3/K5 sizes (108/102/100/34 code lines) and K6 (162/192 without `…HostNext`)
- UH 293/336; item 13's 209+44 (and 241+53 with docstrings)
- item 13's 44 use sites (42 declarations + 2 attribute lines)
- K6's two differences (`Fin 6`/`5` and the loop entry `2`/`3`)
- the one-sided head/tail residues; "Hardness imports SAT"
- FE-LIVE-1 retired; FH-1's in-file copies citing `exists_first_halt`

**Disagreements and gaps:**
1. **Missing exact twin:** `sat_guard_add`/`clA5_guard_add` (16+2 each) is in no family. It is
   used by `satReduction_poly`, `clA5Startup` and `clA5Round`. (Accounting: a minor under
   TEMPLATE.)
2. **Missing kind-4 instance:** `satScanTM/Cfg/_step/_run/_computes` (`SAT:230–301`, 60+10). It is
   the SAT-side analogue of the `clFill*` trio, which the inventory does list.
3. **K3 canonical.** `embedEmitTM` at `castLEEmb` is not a drop-in: R1's transition goes through
   `find?` (§3.2). The inventory does not mention the public `Build/EmitIterEmbed` padding layer.
4. **K5 as public API.** It is not needed; it can be private beside its only consumers (§3.2).
5. **FE-LIVE-1 citation line.** The inventory says `Hardness:7264`; the `exists_first_entry_of_fixed`
   call is at **7252**.
6. **FH-1 "5 of 7 cite `exists_first_halt`".** This cannot be checked in the bundle and conflicts
   with the ledger's closeout row (§7). The bundled r2 resolutions describe `f6d8f0f3`/`6fe6b56c`
   as reader repairs. The inventory places `clockStageCfg_captures` in `ObliviousCandidate`; the
   resolutions name the reader change in `ObliviousSchedule`. Unverified.
7. **Claims about files outside the bundle cannot be verified here.** These are: `Nondeterminism`
   members, lines and imports; `Build/WordTests`, `PolyTimeBlockLoop`, `Build/Seam` and
   `Build/Embed` reachability from `SAT`; `Transducer.lean`'s shape; Embed line numbers. I
   used them only as leads, and flagged each import they imply.
8. **Rule-10 notes the inventory lacks.** These read forms would be exposed once touched:
   - the `PolyTimeComputable` anonymous-constructor and `obtain` reads (in `…_install/_emit`,
     `…Map_poly`, `satSyntax_poly`, `satWidthScan_poly`, `clA5Packed_install`)
   - the definitional reads of the stop adapter's `q₀`/`k` and the host's `k`/`ret` in Hardness
     consumers (finding 2)

---

## 10. Method and limits

- **Extraction.** Bundle sections were split on their `## ===== path =====` headers. Lean bodies
  were taken between the code fences. Line numbers equal the file's own (checked against the
  plan's 4,370 and 8,701 and against 286 inventory entries).
- **Declarations.** A comment- and docstring-stripped column-0 header parse (modifiers,
  `def/lemma/theorem/abbrev/structure/instance`), with a namespace stack. A span ends at the next
  top-level item; trailing blanks are dropped.
- **Twins.** Exact means the comment-stripped code is equal after prefix normalization
  (`sat|Sat ↔ clA5|CLA5`). Near twins use a token `SequenceMatcher` ratio ≥ 0.80 over all
  SAT×Hardness pairs of at least 4 lines.
- **Use sites.** A word-boundary mention of a member's name in another declaration of the same
  file. All members are private, so no other file can mention them.
- **Read forms.** Counts of `rfl`, `change`, `show` and `decide` in proof text. The identifiers in
  `simp`/`simp only`/`simpa`/`dsimp`/`rw`/`unfold` argument lists were classified as same-file
  definitions, same-file lemmas, hypotheses, or other-file definition candidates, then checked by
  hand for the tables above.
- **Limits.** This does not see reads made by anonymous constructors, `obtain`, `exact`
  unification, or `dsimp only` with no arguments. The seal (sealed copy plus `rfl` controls) is the
  authority, and the repair counts above are lower bounds on the number of affected proofs.
- **Not measured.** Copy-screen pair counts, which need `copy-text-screen-v3.py` on the tree;
  replay closure sizes; imports' transitive reach.
