# Three roadmap tracks: F6, book-form Theorem 3.1, Ladner (planning note)

**Status:** read-only planning (sub-agent, 2026-11-06). No tracked file was edited, and Lean was not run.
**Base:** campaign `complexity/arora-barak-ch3-4` at `508781aa` (Lean as at #209/#191/#207's merges).
Line numbers are at this base unless marked otherwise. **The user's ruling** (HANDOFF §3 item 4, 2026-11-06)
is to run all three in parallel. The ruling's own text sets each track's order: F6 is the U2 harvest and
then the fill; the other two tracks are statement phases.

Gate numbers below are placeholders. The next free number is 108 (the last used is 107-rp1-dedup).

---

## Track 1 — F6: `Complexity.space_universal`

### (a) Current state

- **The target.** `TCSlib/Complexity/SpaceComplexity/Hierarchy.lean:150–161`, sorried; in H's delivery
  (`deliver/fill-b6-hierarchy-in`) it is at `:147–158`, byte-preserved. The statement is frozen by RD-3
  (gate 05, PASS 0/0/4) and the B6-hosts gate (13, PASS 0/0/5, which strengthened it to `C · s`).
  `∃ SU, ∀ α, ∃ C, 0 < C ∧ ∀ s x output t, (code.decode α).toFinTM.ComputesInTime x output t →
  spaceUsed … t ≤ s → ∃ t', SU.ComputesInTime (pairEncode (bits s) (pairEncode α x)) output t' ∧
  SU.spaceUsed … t' ≤ C * s`, over the one-tape scheme `TimeHierarchy.code`.
  - No consumer: `space_hierarchy` uses `U₀`. The B6 fill plan places F6 "last".
  - F6 is the last of the 26 headlines (status `campaign/status/2026-11-05-headlines/README.md:15`).
- **Same file, other work.** H's fill was delivered on 2026-11-06 (REPORT `campaign/fills/b6/reports/hierarchy-REPORT.md`):
  - `space_hierarchy` and `LOGSPACE_ssubset_PSPACE` are proved;
  - `SPACE_linear_ne_NP` ends in escalation **E-PAD** (REPORT:510–560): an exact padded-language
    linear-space decider is missing;
  - the delivery changes only `Hierarchy.lean` (+2,295 lines), and its imports gain `SelfUniversal`,
    `Build/WindowRun`, `SpaceComplexity/WindowClock` and `ClassNP/PClosure` (delivery `:11–14`).
  - **Consequence:** after H lands, `Hierarchy` reaches `UniversalK` through `SelfUniversal`
    (`SelfUniversal.lean:8`).
- **The route** (`campaign/fills/b6/drafts/F6-retriage.md`) is U2-E's (`Turing.universalK`,
  `UniversalK.lean:2764`, proved), with two changes: a second header, and a space ledger in place of the
  time bound. Every piece already exists as a **private** of `UniversalK`. Rule 11 forbids citing them,
  and re-deriving them is a duplication finding.
  - Megafill C's Q-U2 says to "publish when `space_universal` is briefed".
  - U2's fill review F7(ii)–(iv) (`campaign/fills/u2s/reviews/universal/REVIEW.md:216`) and its REPORT
    (`universal-REPORT.md:294`) list the promotion candidates.
- **Published hosts F6 also needs** (all proved):
  - `exists_selfStartupTMK` (`UniversalK:1425`, with a space bound `B`) and
    `StepBlock.exists_forwardLoopTM` (`Build/StepBlockForward:481`, with visited-set clauses);
  - `exists_rulerHostTM` (`Build/InputDevice:1226`, a space ledger of the bank plus `ℓ + 2`),
    `pairEncode_drop` (`InputDevice:198`), `pairEncode_pairEncode_length`/`_drop`, and `rewindTM_run_ofCfg`
    (`Build/Rewind:112`);
  - `seamCompTM_step` (`Build/InterpreterStartup:64`), `seamCompTM_spaceUsed_le_add` (`Build/Seam:461`),
    and `vhostSilentTM_runFrom`/`_spaceUsed_le` (`Build/VirtualInput:469/489`);
  - `CodeTM.one_le_spaceUsed` and `length_bits_le_self` (`Encoding`), and `spaceUsed_le_mul_succ` (`Finite`).

### (b) Still to decide or design (the records' open points)

- **D-F6-1, harvest or a private re-derivation** (retriage "Decisions"). The ruling of 2026-10-27,
  "F6 after U2's harvest API PR", already implies harvest first; I recommend confirming it.
- **D-F6-2, the harvest's home** (retriage: "`UniversalK`, or a new `Build/` module if `Hierarchy` should not
  import all of `UniversalK`"). Once H lands, `Hierarchy` imports `UniversalK` transitively, so in-place
  publication costs no import.
  - *Recommended:* publish the scan, seam and suffix-layout rows **in place in `UniversalK`**, whose
    downstream at the tip is 3 modules, plus `Hierarchy` after H.
  - Move the lockstep corollaries beside H2-F in `Build/StepBlockForward` (review F7(ii); downstream 4).
  - Put the `rulerHostCfg` field reader beside `rulerHostCfg` in `Build/InputDevice` (downstream 13).
- **D-F6-3, the startup's input** (retriage's "one open design point"). `exists_selfStartupTMK` reads its
  code at the start of the native input, but in `SU`'s input the code is the second header. The options:
  - (i) the retriage's: a buffered copy of `pairEncode α []`, run through `vhostSilentTM`, at `O(|α|)` cells.
    This needs a new copy leaf, and a full-suffix copy would break `C · s`.
  - (ii) **New, recommended for the route probe:** run the startup under the **ruler host** on the suffix
    `z.drop (2|bits s| + 2) = pairEncode α x`. This is exactly the startup's native input; the ruler is
    the first header's scan, and costs `2|bits s| + 4 ≤ 2s + 4` cells. No copy and no new leaf are needed;
    the ruler is then extended by the second scan.
  - (iii) a startup variant with an input offset: a new host, statement-gated. Not recommended.
- **D-F6-4, the order in `Hierarchy.lean`.** The rule is one fill per file (Q-D3). Three items edit this
  file: H's landing (first, now), F6's fill, and the E-PAD continuation of `SPACE_linear_ne_NP`. The
  record has no ruling on F6 against E-PAD.
- **D-F6-5, RS-1** (`uk_init_mapState`, ledger RS-1: a public row in `TuringMachine/Finite`, with 5 sites in
  4 files). It is not needed by F6. Publishing it in `Finite` means a replay of most of the tree, so
  *recommended:* keep it out of the harvest and leave it to the dedup window.
- The agent: Codex (retriage, step 3). The estimate is 800–1,500 lines (megafill D, T4); with the harvest,
  roughly 500–1,000 (ESTIMATE).

### (c) Next deliverable: the U2 harvest API PR (branch e.g. `lean/u2-harvest-api`; an API gate)

| Public row (proposed name) | Source private (`UniversalK.lean`) | Home | Change |
|---|---|---|---|
| `Turing.headerScanTM (i : Fin k)` + `headerScanCfg` with field equations (or `simps`) | `uk_scanTM :2161`, `uk_scanCfg :2170` | `UniversalK` | visibility; definitions land with their lemmas (policy §1) |
| `Turing.headerScanTM_run` | `uk_scan_run :2370`, already stated "from any input position `1 + p` with `z.drop p = pairEncode u v`" | `UniversalK` | none; `uk_scan_zero/step/pair/header :2180–2310` stay private |
| `Turing.headerScanCfg_ruler` | `uk_scan_ruler :2397` | `UniversalK` | **generalize** from a blank tape to an existing ruler prefix `true^m` before the head, so that two scans give `true^(ℓ₁+ℓ₂)`; `m = 0` is the current statement |
| `Turing.headerRulerTM` + `_run` (scan, then rewind) | `uk_headerTM :2414`, `uk_header_run :2424` | `UniversalK` | visibility (optional; `universalK`'s consumer) |
| `Turing.startupLoopTM` + `_initCfg`, `_live_of_le`, `_runFrom` | `uk_loopTM :1807`, `uk_loop_init :1827`, `uk_loop_pre_live :1834`, `uk_loop_run :1850` | `UniversalK` | visibility |
| `Turing.startupLoopTM_spaceUsed_le` | `uk_loop_space :1954` | `UniversalK` | **generalize**: today it fixes the native startup's endpoint (`hrun` at input position 1, with no ruler). Restate it, like `uk_loop_run`, for any seam endpoint `d` with `d.mapState (fun _ => entry) = embedEmitCfg σ … c`, so that it serves the `k + 1` suffix layout |
| `StepBlock.forwardLoopCfg_init_workTapes`, `_init_fields`, `_halt_iff`; `embedEmitCfg_forwardLoop_init` | `uk_encode_init_tapes :1697`, `uk_encode_init_fields :1736`, `uk_encode_halt :1752`, `uk_embed_init :1766` | `Build/StepBlockForward` (the `_halt` lemma is needed by the converse below) | visibility |
| `StepBlock.forwardLoop_forward`, `_live`, `_converse` | `uk_loop_forward :1871`, `uk_loop_live :1896`, `uk_loop_converse :1918` | `Build/StepBlockForward`, beside H2-F | visibility; generic in `M`, `L` and `cost` |
| `Turing.suffixRulerCfg` + field equations; `suffixRulerCfg_embed` | `uk_suffixCfg :2504` (generic in `z`, `ℓ`), `uk_embed_suffix :2672` | `UniversalK` | visibility |
| `Turing.rulerHostCfg_fields` | `uk_ruler_fields :2651` | `Build/InputDevice`, beside `rulerHostCfg` | visibility |

- **Unchanged.** `universalK` and `exists_selfUniversalK` are re-pointed to the public rows, with their
  statements byte-identical. `uk_suffixStartupTM`/`_run` (`:2496/2520`) stay private: they are U2-E's own
  native-startup composition. All names are proposals, to be name-searched on every ref (WORKFLOW §3).
- **Gate pack outline**, after gate 73 (U2's API) and gate 20 (the H1 harvest precedent):
  - why: rule 11, and harvest before the second consumer is briefed;
  - a "what changed" table of row ← private, with each generalization argued;
  - the freeze: every public statement unchanged, with only bodies re-pointed;
  - rule 10, the sealed copies with controls;
  - axioms: every new row on the standard three;
  - a **consumer probe**: F6's route composed from the published rows (two scans, the startup under the
    ruler host, the ruler host around H2-F, the space ledger), with only F6's own leaves sorried;
  - the v3 screen (pairs moved or gone, none new), names on every ref, and lint check 8;
  - the replay: the downstream of `UniversalK`, `StepBlockForward` and `InputDevice`, chained from the
    campaign snapshot. If H has merged, `Hierarchy` is included.
- **Then F6's brief** (Codex), issued on H's merged tree. It authorizes the import union; the expected
  set is none beyond H's nine, to be confirmed by the import probe. The pre-ship has the route probe
  for D-F6-3 (ii), the seal controls, the screen base and the base sorry set.

### (d) Overlaps

- **`lean/dedup-ro1`** (parked, `7c940a8a`): the user ruled to re-point **every** site. RO-1's list names
  `UniversalK`'s fixed-machine statements, and `UniversalK:2291` lies inside `uk_scan_pair`, a harvested
  private. This is a textual conflict, so one goes first; *recommended:* the harvest first, then RO-1
  re-points the published row. RO-1 also touches `TwoTapes` (`tt_round`, ledger +1 from #211).
- **H's landing:** the same downstream (`Hierarchy`). Whichever merges second takes a merged-tree replay.
- **#211** (`TwoTapes` only) and **#212–#216**: no file overlap. NatBits (after #208) moves
  `length_bits_le_self` to `TuringMachine/NatBits` with its name kept, and its 340-module replay
  includes `UniversalK`, so it needs a merged-tree replay with the harvest.

---

## Track 2 — book-form Theorem 3.1 (the `f log f` time hierarchy)

### (a) Current state, and what "book-form" means in the records

- **The received theorem.** `Complexity.time_hierarchy` (`TimeHierarchy/Diagonal.lean:518`, proved) says
  that if `TimeConstructible g` and `∀ A, ∃ N, ∀ n ≥ N, A * (f n + n + 1)^2 ≤ g n`, then
  `DTIME f ⊂ DTIME (g + 1)`. `_of_pos` (`:531`) gives `DTIME g`. Its divergences are recorded at `:67–98`:
  - a **quadratic overhead**, owing to the one-work-tape normal form;
  - `DTIME(n) ⊊ DTIME(n^1.5)` is not derivable (`:84–88`);
  - "the sharper `f log f` form is planned … not available until those exist" (`:79–83`).
  - The facade `TimeHierarchy.lean:13–17` says "quadratic overhead in place of the book's `f log f`".
- **"Book-form"** is defined in plan §2.1 (CH34-Q3, "strengthen", 2026-10-08): Theorem 3.1 at the book's
  `f log f = o(g)`, via Hennie–Stearns plus the two-tape universal. "Until that lands, the received form
  is documented as delivered strength, never as Thm 3.1 verbatim." The U2 design §3.2 specifies
  `time_hierarchy_book : n ≤ f n ∧ f log f = o(g)`, and the G5 plan (lines 3–5) refers to it as
  "book-form Theorem 3.1".
- **Diagonal Part 1 has landed** (#100, gate 24, PASS 0/0/2): `DiagSimulator` (`:212`) with `.mono`,
  `.diagLang_not_mem_DTIME`, `.time_hierarchy` and `_of_pos` (`:226–310`); `SelfSimulator` (`:341`);
  `.toDiagSimulator` (`:364`); and the `f²` instance `oneTapeSelfSimulator`/`sqDiagSimulator` (`:429/465`).
- **Part 2 is the book form**, which the 2026-10-14 authorization places at the end of `Diagonal.lean`
  (Hydroxyi's file). It is drafted and proved in the U2 probe, `campaign/items/u2/probes/U2DiagParam.lean.txt`:
  - `:275–330`: `logOverhead`, `logDiagOverhead`, `le_logDiagOverhead`, `logOverhead_add_le`,
    `time_hierarchy_log`, `logDiagOverhead_le_book` and `time_hierarchy_book`;
  - `:681–742`: `log_mul_two_pow`, `logOverhead_mul_le`, `code₂` and `twoTapeSelfSimulator`.
- **Inputs.**
  - `two_work_tapes_run`/`_binary`: at the base, `Robustness/TwoTapes.lean:64/78`, sorried at `:70`. On
    #211's head (`e7e78aaf`) they are at `:2428/2452` with **no `sorry`**.
  - `exists_selfUniversalK` (`UniversalK:2052`) and `universalK` (`:2764`) are **proved** (no `sorry` in
    `UniversalK`).
  - `exists_effectiveMachineCode2` (`Codes2Tape:253`) and `exists_code2TM` (`:345`) are proved.
  - `Turing.universal_TlogT` (`UniversalTlogT.lean:57`) is proved from `two_work_tapes_run`.
- **A correction to the brief's framing.** The book-form chain does **not** go through `universal_TlogT`.
  Per U2 design Q1 (ruled as recommended), the simulator is the self-application U2-U at `k = 2`
  (`exists_selfUniversalK 2`), not the code-first U2-E plus `preTM`. Both depend on the same single
  admission, `two_work_tapes_run`. **The real prerequisite is therefore #211**, whose gate 102 round 2 is
  **HOLD 0/0/2** (`gates/102-g5-landing-fill/findings-r2.md`): the zero-time sweep in `Loop` and
  `Advice`, and NZ-1's four members. A round 3 is due.

### (b) To decide or design

- **Already ruled** (2026-10-14, "all as recommended"):
  - Q7: state both forms, with the book form under `∀ n, n ≤ f n` rather than `TimeConstructible f`;
  - Q8: the home is the end of `Diagonal.lean`, with Hydroxyi's file authorized;
  - Q10: the illustration `DTIME(n+1) ⊊ DTIME((n+1)²)` is **dropped**;
  - Q4: no U2-V;
  - the facade sentence is fixed in this PR (gate 24's ruling 4).
- **Carried.** Gate 24 asks for compiled sanity checks in this PR (`resolutions.md:58–62`):
  `¬ Nonempty (DiagSimulator (fun _ _ => 0))`, `¬ Nonempty (SelfSimulator (fun _ => 0))`, no
  `SelfSimulator` with a constant `decode`, and the `rfl` projections of `mono`/`toDiagSimulator`.
- **Re-route the probe's simulator.** The probe built `twoTapeSelfSimulator.W` from U2-V
  (`exists_selfVerdictTMK`), which was never landed. It must use
  `Classical.choose (exists_selfUniversalK 2 code₂.toK)`: the forward clause's `C*(t+1)` is at most
  `C*(t + |pairEncode α w| + 1)`, bridged by `EffectiveMachineCode2.toK_toFinTM`. This is a small
  re-proof; the design (§2.2) says U2-U implies the one-bit form.
- **The definitions rule** (policy §1, 2026-10-16) postdates the design. `logOverhead`, `logDiagOverhead`
  and `code₂` each need an `_eq` lemma, and `twoTapeSelfSimulator` needs projection lemmas (`_W`, `_decode`,
  `rfl`) like `sqDiagSimulator_W`.
- **Statement shape.** *Recommended:* write the headline hypotheses expanded, as `time_hierarchy` does,
  and keep `logDiagOverhead` only in the generic layer.
- **Open for the user:**
  - **T31-1, timing.** (A) Land after #211 merges, so the gate audits an admission-free result
    (*recommended*: its only admission would otherwise be `two_work_tapes_run`, and the replay chains
    from the merged snapshot). (B) Land now, with `sorryAx` through `two_work_tapes_run` until #211 merges.
  - **T31-2, `_of_pos`.** Add `time_hierarchy_book_of_pos`, `DTIME f ⊂ DTIME g` for positive `g` (the
    book's literal class)? *Recommended: yes*, mirroring `time_hierarchy_of_pos`. This is a new
    statement, beside Q7.
  - **T31-3, Theorem 1.9's literal code quantifier** (Q11) stays relaxed. `DTIME(n) ⊊ DTIME(n^1.5)` (Q10)
    stays in the backlog: it needs a time-constructibility witness for `n·⌊√n⌋`.

### (c) Next deliverable: the Part 2 PR plus a statement gate

**Edits to `TimeHierarchy/Diagonal.lean`.** New declarations in namespace `Complexity.TimeHierarchy`:
- `logOverhead`, `logOverhead_eq`, `logDiagOverhead`, `logDiagOverhead_eq`, `le_logDiagOverhead`,
  `logOverhead_add_le` and `logOverhead_mul_le` (with `log_mul_two_pow`, private unless Mathlib has it);
- `logDiagOverhead_le_book`;
- `code₂ : EffectiveMachineCode2 := Classical.choice exists_effectiveMachineCode2` and `code₂_eq`;
- `twoTapeSelfSimulator : SelfSimulator logOverhead`, with its `_W` and `_decode` projections.

The public statements, in namespace `Complexity`, beside `time_hierarchy`:

```lean
theorem time_hierarchy_log {f g : ℕ → ℕ} (hg : TimeConstructible g)
    (hfg : ∀ A : ℕ, ∃ N, ∀ n ≥ N,
      A * ((f n + n + 1) * (Nat.log 2 (f n + n + 1) + 1)) ≤ g n) :
    DTIME f ⊂ DTIME (fun n => g n + 1)
theorem time_hierarchy_book {f g : ℕ → ℕ} (hg : TimeConstructible g) (hf : ∀ n, n ≤ f n)
    (hfg : ∀ A : ℕ, ∃ N, ∀ n ≥ N, A * (f n * Nat.log 2 (f n)) ≤ g n) :
    DTIME f ⊂ DTIME (fun n => g n + 1)
theorem time_hierarchy_book_of_pos {f g : ℕ → ℕ} (hg : TimeConstructible g) (hpos : ∀ n, 0 < g n)
    (hf : ∀ n, n ≤ f n) (hfg : ∀ A : ℕ, ∃ N, ∀ n ≥ N, A * (f n * Nat.log 2 (f n)) ≤ g n) :
    DTIME f ⊂ DTIME g          -- T31-2
```

- Proofs:
  - `time_hierarchy_log`: `(twoTapeSelfSimulator.toDiagSimulator.mono 2 logOverhead_add_le).time_hierarchy le_logDiagOverhead hg hfg`;
  - `time_hierarchy_book`: from `time_hierarchy_log` with `logDiagOverhead_le_book` at `12 · A`;
  - `twoTapeSelfSimulator.normalForm`: `two_work_tapes_binary`, `exists_code2TM`, `MachineCode2.decode_encode`
    and `logOverhead_mul_le`.
- Existing declarations stay verbatim. Imports gain `TuringMachine.UniversalK`,
  `TuringMachine.Robustness.TwoTapes` (`Codes2Tape` comes through `UniversalK`) and `Mathlib.Data.Nat.Log`
  if it is not already reached.
- **The import graph** has no cycle: neither closure contains `Diagonal` (`UniversalK` has 57 modules,
  `TwoTapes` 24). `Diagonal`'s downstream is 13 modules, which inherit the two.
- **Docstrings:**
  - rewrite `Diagonal`'s "Divergences" section (`:67–98`) and its main results;
  - rewrite the facade `TimeHierarchy.lean:13–17`, "quadratic overhead in place of the book's `f log f`",
    to name `time_hierarchy_book`;
  - add no campaign labels (WORKFLOW §2).
- **The gate pack outline** follows gate 92 and gate 24:
  1. the statements against [AB09, Thm 3.1, pp. 69–70], including:
     - `f log f = o(g)` read as "for every `A`, eventually";
     - `hf : n ≤ f n` in place of `TimeConstructible f`;
     - `DTIME (g + 1)` together with `_of_pos`;
     - `Nat.log 2` and the case `f n ≤ 1`;
  2. the self-simulator's two clauses, and the absorption arithmetic;
  3. axioms: the standard three if after #211, else `sorryAx` only through `two_work_tapes_run`;
  4. rule 10, sealing `DTIME`, `TimeConstructible`, the `SelfSimulator`/`DiagSimulator` fields,
     `EffectiveCodeK.toFinTM`, `ComputesInTime` and the new definitions;
  5. the freeze: every existing public declaration of `Diagonal`, including `diagLang`'s body and
     `diag_cost_le`, is byte-identical;
  6. gate 24's carried sanity checks, as `example`s in an evidence probe;
  7. the screen against `oneTapeSelfSimulator` (an expected idiom pair; disclose it), names, and lint check 8;
  8. the replay: `Diagonal`'s downstream from the campaign snapshot;
  9. FYI to Hydroxyi, since the file is theirs.

### (d) Overlaps

- **#211:** the dependency, per T31-1.
- **The F6 harvest:** both touch `UniversalK`'s closure but not the same file. `UniversalK` gains rows and
  loses nothing public, so whichever merges second takes a merged-tree replay.
- **H's landing:** `Hierarchy` imports `Diagonal`, so its closure grows by `TwoTapes`; this is a replay
  consideration only.
- **RO-1 (parked):** it touches `TwoTapes`, not `Diagonal`. **#208, #212–#216:** none.

---

## Track 3 — Ladner's theorem ([AB09, Theorem 3.3]; P3.4)

### (a) Current state

- **Nothing is stated.** There is no `Ladner.lean` and no `SAT_H` (`git grep` finds only the records).
  The plan is `campaign/design/plans/AroraBarakChapters3-4Plan.md`:
  - §1:41: "Thm 3.3 Ladner, its Claim, and Ex 3.6(a)(b) — Missing — core-late (P3.4)";
  - §3:235: the home is `Diagonalization/Ladner.lean`;
  - §4:259: "`SAT_H`; Ex 3.6(a) (`H` in polynomial time); the Claim; Ex 3.6(b); Thm 3.3 — ~6";
  - §6:994: summit 4, "Ladner's `H` in polynomial time";
  - §7:1028: CH34-Q6, core-late.
- The backlog entry is `campaign/backlog.md:3756–3767`. It consumes the closed SAT surface and the
  `polyTimeComputable` layer, is independent of P3.3, and **was on hold** (user, 2026-10-09). It is now
  started (2026-11-06).
- **Existing surface, by exact name:**
  - `Complexity.SAT` (`ClassNP/SAT.lean:115`; the total decoder, so **every malformed string is in SAT**);
  - `SAT_mem_NP` (`:954`) and `SAT_NPComplete` (`CookLevin/Hardness.lean:8765`);
  - `P` (`ClassP/P.lean:57`, `⋃ c, DTIME (n^c + 1)`) and `NP` (`ClassNP/NP.lean:82`);
  - `PolyTimeComputable` (`ClassNP/PolyTime.lean:69`) and `.comp` (`:149`);
  - `PolyTimeReducible`, with scoped `≤ₚ` (`ClassNP/Reductions.lean:55/58`);
  - `NPHard`, `NPComplete` (`:124/128`), `mem_P_of_polyTimeReducible` (`:98`), `P_eq_NP_of_NPHard_mem_P`
    (`:136`) and `NPComplete.mem_P_iff` (`:146`);
  - `preimage_mem_P`, `inter_mem_P` and `preimage_mem_NP` (`ClassNP/PClosure.lean:71/91/215`);
  - `DTIME` (`ClassP/DTIME.lean:88`) and `TimeConstructible` (`ClassP/TimeConstructible.lean:74`);
  - the FP toolkit `polyTimeComputable_iterate`/`_guardLoop` (`ClassP/BinaryArith/Iterate.lean:160/190`);
  - **the uniform scheme** `Complexity.expCode : UniformMachineCode` (`Diagonalization/EXPCOM.lean:178`).
    Its jointly polynomial bounded-acceptance simulator is defined at `:105–125` and proved at `:156`.
  - `MachineCode.decode_encode_pad` (`Encoding.lean:656`, "every machine has infinitely many codes").
- **The precedent for "`H` polynomial-time":**
  `PolyTimeComputable (fun z => Nat.bits (lovaszPrime z.length))` (`ClassP/BinaryArith/PrimeFind.lean:443`).

### (b) To design (the statement phase's decisions; recommendations in italics)

- **LD-1, the enumeration `M_i`.**
  - The per-code constants of `Turing.universal`/`timed_universal` (an arbitrary `canonizerTime`) would
    make `H` non-polynomial.
  - *Use `M_i := (expCode.decode (Nat.bits i)).toFinTM`*: `expCode`'s simulator is uniform in the code.
  - Every machine has infinitely many indices: `encode M ++ true^(m+1)` ends in `true`, so it is a
    `Nat.bits i`. This is a fill lemma.
- **LD-2, the simulation predicate and the budget.**
  - *Use the acceptance reading: "for all `x` with `|x| ≤ log n`,
    `M_i.ComputesInTime x [true] (i * |x|^i) ↔ x ∈ SAT_H`"*. It matches the simulator's interface
    (`simulator_accepts`/`_rejects`) and `EXPCOM`'s "outputs 1" reading.
  - **A false-statement trap:** the book's literal "outputs `SAT_H(x)`" with the budget `i·|x|^i` gives a
    budget of 0 at `x = []`. No machine halts in 0 steps (`not_computesInTime_zero`), so `H(n) = log log n`
    for every `n`, and the Claim fails.
  - Under the acceptance reading `[] ∉ SAT_H`, so both sides are false and the trap disappears. The
    alternative is the budget `i·(|x|+1)^i`. The gate must check the edge cases `x = []`, `i = 0`, and
    `n < 16`, where `log log n ≤ 1`.
- **LD-3, the pad.** *The book's literal `ψ ++ false :: List.replicate (|ψ|^(H |ψ|)) true`, which splits
  uniquely at its last `false`.* The alternative is `pairEncode ψ (true^…)`, which would align with E-PAD's
  interface (REPORT:518) and the `pairFstD`/`pairSndD` FP lemmas; it is a declared deviation if chosen.
- **LD-4, logarithms.** *`Nat.log 2 (Nat.log 2 n)` and `Nat.log 2 n` (floors)*, as `Diagonal` uses `Nat.log 2`.
- **LD-5, the definition of `H`.** *Use strong recursion on `n` through a parametric
  `padSAT (h : ℕ → ℕ) : Language Bool`.*
  - Membership of strings of length `≤ log n < n` needs `h` only below `n`.
  - `ladnerH n := if ∃ i < log log n, Good i n then Nat.find … else log log n` (noncomputable, classical).
  - **Reading lemmas are proved at skeleton time** (workflow §2's allowed unfolding lemmas, flagged in
    the pack): `ladnerH_eq`, `padSAT_congr` (agreement below a length), `mem_padSAT_iff`, and
    `ladnerH_le` (`≤ log log n`).
- **LD-6, Ex 3.6(b)'s statement.** *General in `h`:* `PolyTimeComputable (bits ∘ h ∘ length)`, `h → ∞`,
  `NPHard (padSAT h) → SAT ∈ P`. `NPHard` is strictly stronger than the book's `NPComplete` hypothesis;
  this is a declared strengthening. The book's form is the alternative.
- **LD-7, the shape of Theorem 3.3.** *Both*:
  - `ladner : P ≠ NP → ∃ L ∈ NP, L ∉ P ∧ ¬ NPComplete L` (the book's statement);
  - the witness form `SAT_H_intermediate : P ≠ NP → SAT_H ∈ NP ∧ SAT_H ∉ P ∧ ¬ NPComplete SAT_H`.
- **LD-8, source check (attribution, policy §2).** The plan's "Ex 3.6(a)(b)" collides with the library's
  "Example 3.6(1)–(3)" (the oracle claims, `ClassOracle/SATOracle.lean:15`). Before drafting docstrings,
  pin Theorem 3.3's Claim and Exercise 3.6's two parts against the book (pp. 71–72 and the chapter's
  exercises). My reading is that (a) is "`H` is polynomial-time computable" and (b) is "for polynomial-time
  `H → ∞`, `SAT_H` `NP`-complete ⇒ `SAT ∈ P`"; this is unverified.
- **LD-9, hosts** (workflow §2: a sketch names its hosts; an unregistered host is not ready). The sketch
  of Ex 3.6(a) needs two things:
  - (i) an FP-level call of `expCode.simulator` with a **poly-bounded** budget, since the simulator is
    polynomial in the *value* `t` and `t` is given in binary;
  - (ii) brute-force `SAT` on strings of length `≤ log n` in time `poly(n)`.
  - Survey both before the gate. If either is missing, it is a host statement item of this phase, like
    E-PAD. Candidates are `NP_subset_EXP` (`ClassNP/EXP.lean:2488`), `EXPCOM`'s internal calls and the FP
    toolkit.
- **LD-10, homes.**
  - *New `Diagonalization/Ladner.lean`*, namespace `Complexity` (auxiliaries under `Complexity.Ladner`
    or private).
  - Imports: `ClassNP.Reductions`, `ClassNP.PClosure`, `CookLevin.Hardness` (`SAT_NPComplete`; the
    statements do not need it, but the fill does), `Diagonalization.EXPCOM` (`expCode`) and
    `Mathlib.Data.Nat.Log`.
  - The facade `Diagonalization.lean` gains the import and a Contents line. Its docstring already carries
    one campaign label, "decision CH34-Q8" (`:22`), which belongs to the deferred docstring cleanup.

### (c) Next deliverable: the statement file and its gate

`Diagonalization/Ladner.lean`. Definitions with proved readings, then **six sorried statements** (the
plan's count is about 6):

```lean
def padSAT (h : ℕ → ℕ) : Language Bool :=
  {y | ∃ ψ ∈ SAT, y = ψ ++ false :: List.replicate (ψ.length ^ h ψ.length) true}   -- LD-3
noncomputable def ladnerMachine (i : ℕ) : FinTM Bool := (expCode.decode (Nat.bits i)).toFinTM -- LD-1
noncomputable def ladnerH : ℕ → ℕ := …        -- LD-5; proved: ladnerH_eq, ladnerH_le, padSAT_congr
noncomputable def SAT_H : Language Bool := padSAT ladnerH          -- + SAT_H_eq (rfl)

theorem ladnerH_polyTime : PolyTimeComputable (fun x => Nat.bits (ladnerH x.length))  -- Ex 3.6(a)
theorem SAT_H_mem_NP : SAT_H ∈ NP
theorem ladnerH_bounded_of_mem_P : SAT_H ∈ P → ∃ C, ∀ n, ladnerH n ≤ C               -- Claim (1)
theorem ladnerH_unbounded_of_not_mem_P : SAT_H ∉ P → ∀ C, ∃ N, ∀ n ≥ N, C ≤ ladnerH n -- Claim (2)
theorem SAT_mem_P_of_padSAT_NPHard {h : ℕ → ℕ}
    (hp : PolyTimeComputable (fun x => Nat.bits (h x.length)))
    (hu : ∀ C, ∃ N, ∀ n ≥ N, C ≤ h n) (hH : NPHard (padSAT h)) : SAT ∈ P        -- Ex 3.6(b), LD-6
theorem SAT_H_intermediate (h : P ≠ NP) : SAT_H ∈ NP ∧ SAT_H ∉ P ∧ ¬ NPComplete SAT_H -- Thm 3.3
theorem ladner (h : P ≠ NP) : ∃ L ∈ NP, L ∉ P ∧ ¬ NPComplete L                      -- Thm 3.3
```

Six statements are sorried. `ladner` is proved in one line from `SAT_H_intermediate`. An optional seventh
obligation is `SAT_reducible_padSAT_of_bounded` (`h` bounded and
polynomial-time ⇒ `SAT ≤ₚ padSAT h`), which `SAT_H_intermediate`'s sketch needs.

**The sketches name their obligations:**
- Ex 3.6(a): memoized `H` below `log n`, the bounded-acceptance calls (LD-9 (i)), brute-force SAT
  (LD-9 (ii)), and the arithmetic `i·(log n)^i ≤ n^{O(1)}` for `i < log log n`.
- Claim (1): a code of an `expCode` normal form of the `P`-decider, with an index above its time degree.
- Claim (2): each `M_i` fails at some `x_i`, otherwise `SAT_H ∈ P` via the uniform simulator; so `H(n) ≠ i`
  once `log n ≥ |x_i|`.
- Ex 3.6(b): the reduction's output shrinks `ψ` to `|ψ'| ≤ |ψ|^{1/2}` once `h > 2i`; recurse.
- Theorem 3.3: `SAT_NPComplete`, `NPComplete.mem_P_iff`, Claim (1) together with the bounded pad
  reduction, Claim (2) together with Ex 3.6(b).

**The gate pack outline** follows ch4-p43 (a statement-program phase) and gate 26:
1. the inventory, and the definitions verbatim;
2. the deviations declared: the LD-2 acceptance reading, the LD-1 uniform enumeration, `NPHard` for
   (b), and the total `SAT` decoder;
3. the brief:
   - faithfulness to [AB09, Thm 3.3 and proof];
   - the recursion's well-definedness;
   - the truth of each statement (the Claim's directions; argue (b) constructively);
   - the edge cases of LD-2;
   - non-vacuity checks (`padSAT` nonempty; `ladnerH_le`; `SAT_H ≠ ∅`);
   - the skeleton-time proofs, which are part of the audited surface;
4. hosts (LD-9) against the `machine-library-design.md` §14 registry;
5. axioms: `sorryAx` only in the six sorried statements (and through them in `ladner`), and the readings
   standard;
6. rule 10, the seal for the proved readings;
7. the freeze: no existing statement changes, and the facade wiring;
8. names, screen and lint check 8;
9. the elaboration and the replay: the new module, the facade and the root;
10. the open questions LD-1 to LD-8, for the user after the findings.

**The route note first.** Before the file, write a short design note at `campaign/items/ladner/LADNER-design.md`
with the LD-* decisions and a probe that elaborates the definitions and readings. Have the user rule the
LD-* decisions, then draft.

### (d) Overlaps

- **None blocking.** No open PR touches `Diagonalization/`, `ClassNP/{SAT,Reductions,PClosure}` or `EXPCOM`.
- **`lean/dedup-ro1`** touches `ClassNP/SAT.lean` (`satRed_one`, privates only), so Ladner's citations are
  unaffected.
- **NatBits** keeps the names of the `Nat.bits` lemmas.
- **E-PAD** (H's escalation) also designs padding. If its host lands as a general padding/validation row,
  Ladner may cite it (LD-3's `pairEncode` option). Coordinate the shape before either gate.

---

## (e) Rulings needed from the user

1. **D-F6-2, the harvest's homes:** in place in `UniversalK`, with the corollaries in `StepBlockForward`
   and `InputDevice`? *Recommended: yes.* D-F6-1 (harvest first) is to be confirmed.
2. **D-F6-3, F6's startup route:** the ruler host on the first header's suffix (new, *recommended*) or the
   retriage's buffered copy? This can be decided after the harvest's consumer probe.
3. **D-F6-4, the order in `Hierarchy.lean`:** after H's landing, F6's fill or E-PAD's continuation of
   `SPACE_linear_ne_NP` first? One fill per file.
4. **RO-1 against the harvest:** both edit `UniversalK` (`:2291` is inside a harvested private). *The harvest
   first.* RO-1's two parked questions (ledger RO-1) still stand.
5. **T31-1:** land the book-form PR after #211 merges, admission-free (*recommended*), or now with `sorryAx`?
   **T31-2:** add `time_hierarchy_book_of_pos`?
6. **Ladner's LD-1 to LD-7** (the enumeration, the acceptance reading and budget, the pad form, the
   recursion, (b)'s generality and `NPHard`, Theorem 3.3's shape), and **LD-8**, the source check of
   Exercise 3.6 against the book.
7. **The agents:** Codex for F6 (the retriage). The book-form PR is the maintainer's (about 150–220 lines;
   U2 design §6 item 7). Ladner's fill comes later and needs an agent.


## (f) The user's rulings (2026-11-06)

1. **D-F6-2:** the harvested rows go in a new `Build/` module, not in place in `UniversalK`. D-F6-1: the harvest comes first, before RO-1's `UniversalK` edits (option "RO-1 first" not taken).
2. **D-F6-3:** open; decide after the harvest's consumer probe.
3. **D-F6-4:** E-PAD's continuation of `SPACE_linear_ne_NP` first, then F6's fill.
4. **T31-1/T31-2:** after #211 merges, admission-free, with `time_hierarchy_book_of_pos`.
5. **Ladner:** LD-1 to LD-7 as recommended; LD-8 is the maintainer's source check before docstrings.

**LD-8 (the maintainer, 2026-11-06).** The book's text of Exercise 3.6 could not be fetched from this
session (network policy). Course notes (Princeton COS 522 hw6, Cornell CS 6810 lec. 3/4) confirm the
book's own pointer: "the definition of `H` implies an `O(n³)`-time recursive algorithm that computes
`H(n)` from `n` (see Exercise 3.6)". So `ladnerH_polyTime` is Exercise 3.6's first part. The second
part's wording is unpinned. Until it is pinned against the book, docstrings cite
[AB09, Theorem 3.3 and its proof] for the Claim and for `H → ∞`, and give no exercise part letter
beyond the `O(n³)` computation.

**E-PAD (the user, 2026-11-06):** the API fill publishes a **general** `mem_SPACE_pad` (any space
bound, a polynomial unary pad) in a **new `SpaceComplexity/Padding`** module. It is meant for later
reuse by Ladner's padding. `Hierarchy.lean` may import it, and the maintainer closes
`SPACE_linear_ne_NP` (`sph_linear_ne_NP_of_padding space_hierarchy <E-PAD>`) in a small PR with its
own gate, not through a fill. The fill is dispatched by pasted prompt (WORKFLOW §5).
