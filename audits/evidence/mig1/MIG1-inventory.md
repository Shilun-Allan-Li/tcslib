# MIG-1 inventory: existential rows, the `f2_` region, the R3 canonical rows

> **Maintainer note (2026-10-13).** A maintainer sub-agent wrote this file against the read-only
> checkout `wt-mig1` of campaign commit `6aa9f67bc0b3181672d50eacb9d172e468070df3`. In the
> repository, `MIG1Draft.lean` is `audits/evidence/mig1/MIG1Draft.lean.txt`, `elaboration.log` is
> `audits/logs/mig1-draft-elaboration.log`, and the measurement scripts `work/*.py` are
> `audits/evidence/mig1/scripts/`; their data files are not kept. MIG-0a has since landed
> (PR #83) with the imports cited here, and MIG-0b's gate is issued (`audits/mig0b-pack.md`).

Measured at the campaign tip in the read-only checkout `wt-mig1` (scratchpad), 2026-10-13. Every
count below comes from the scripts in `mig1/work/` (all run as `python3 -I`, listed in §6), over
the Lean sources with comments and docstrings handled as stated. Line numbers are those of the
checkout. "P" marks a `private` declaration. Nothing in the checkout was edited.

## 0. The backlog row's figures against the code

| Figure (backlog MIG-1) | Backlog | Measured | Verdict |
|---|---|---|---|
| Existential rows | 66 | **53** public rows of the eight named files whose conclusion begins with `∃` over a machine: 34 home rows (Primitives 18, Composition 7, Loop 6, Wrappers 1, Encoding 2, Simulation 0, TimeConstructible 0) and 19 Catalog space rows. One more existential hides in a definition: `Complexity.timeConstructible_id : TimeConstructible id`, whose `TimeConstructible` unfolds to `∃ c, 0 < c ∧ ∃ M, …` (TimeConstructible:68) | **not reproduced** (see note a) |
| `f2_` copies | 304 | **304** declarations named `f2_*`, all private, between lines 1787 and 10678 of `Build/Catalog.lean` | **reproduced** |
| Verbatim lines of the copies | 6,255 | No method reproduces 6,255. **232** of the 304 are code-identical to a same-named declaration of a home file once the prefix is removed (4,351 lines with docstrings); 25 more have a same-named source but differ; 47 have none. Line-level measures: table in note b | **not reproduced** |
| Space rows | 22 | **22** public declarations in the region (lines 1779–11361), but only **20** are space rows: 19 existential space rows and `redirectTM_spaceUsedByTape`; the other two, `rewind_scan_heads` and `rewind_heads`, are head-position lemmas about Simulation's rewind. Catalog has 6 more public space statements outside the region (`capture_visitedByTapeHead` and the five R3 `_spaceUsedByTape` rows) | **count reproduced, description corrected** |
| R3 canonical `_run` rows | 0 external consumers | 6 rows, 237 lines with docstrings. **5 external citations in 2 files**: `copyTM_run` at `Build/CertShell.lean:571` and `TuringMachine/CodeSimulator.lean:1291`; `transferTM_run` at `Build/CertShell.lean:585, 589, 602`. The other four rows have none | **not reproduced** (§3) |
| Region | about lines 1785–11365 | `namespace Turing.FinTM` at 1779, first `f2_` docstring at 1785, `end Turing.FinTM` at 11361: 9,583 lines | consistent |

**Note a (the 66).** Neither the machine-existential count nor any natural variant gives 66:

| Population | Count |
|---|---|
| Public declarations of the eight files with a conclusion beginning `∃` over a machine | 53 |
| … plus `timeConstructible_id` | 54 |
| … including private machine-existential lemmas (6 in Catalog, 5 in Primitives) | 64 |
| Public declarations of the eight files with a conclusion beginning `∃` of any kind (adds the 6 R3 `∃ T ≤ …` rows, `compareTM_run_ofCfg`, `rewind_heads`, `loop_run`, `pairDecode_eq_none` and Simulation's 5) | 68 |
| Public machine-existential rows in all of `TuringMachine/Build/*`, `TuringMachine/*` and `ClassP/*` | 81 |

The design (`MIG1-design.md`) covers the 53 rows and `timeConstructible_id`.

**Note b (the verbatim lines).** The 304 copies span 6,113 lines of code (from the declaration
keyword to the next top-level command) and 6,929 with their docstrings.

| Method | Code lines | With docstrings |
|---|---|---|
| Whole declarations code-identical to the same-named source after removing `f2_` (232 declarations) | — | 4,351 |
| Longest-common-subsequence line match against the same-named source (257 pairs) | 4,614 | 5,293 |
| The same, plus the best-matching source declaration for the 47 without a same-named source | 4,904 | 5,583 |
| Lines (stripped, prefix removed) that occur anywhere in the seven home files | 5,244 | 5,934 |
| The same, exact indentation | — | 5,827 |

Design §16 attributes the migration's figures to seven read-only reviews of the tip `9827cc99`;
the method behind 6,255 is not recorded there or in the backlog. The region has changed since
its fill: the F2 gate's audit counted exactly 306 `f2_*` declarations
(`audits/routine-f2-findings.md:35`), today there are 304, and which two went was not traced.
Without git history the measurement cannot be replayed at that tip.

## 1. The existential rows of MIG-1's files

Population: every public `theorem`/`lemma` of `Build/Catalog`, `Build/Primitives`,
`TuringMachine/Composition`, `Build/Loop`, `Build/Wrappers`, `TuringMachine/Encoding`,
`TuringMachine/Simulation` and `ClassP/TimeConstructible` whose conclusion, after its binders,
begins with `∃` whose first binder group mentions `FinTM`, `MultiTapeTM` or `CodeTM`
(`exrows.py`, `mclass.py`). Simulation has none (its five `∃` rows quantify times or
configurations). Consumers: every identifier occurrence in comment-stripped code of all 623
`TCSlib` modules, qualified or not, excluding the declaration itself (`consumers.py`); a check
over the whole tree found every row name declared exactly once, so the matches are unambiguous.
"Internal" counts uses in the row's own file; "doc" counts mentions in comments or docstrings
of other files.

| Row (file:line) | Name | Statement shape | Witness today | Internal | External cites / files | External files | Doc |
|---|---|---|---|---|---|---|---|
| Catalog:4226 | `computesFunInTime_id_spaceUsed` | `∃ (M : FinTM Bool) (c : ℕ), M.ComputesFunInTime id (fun n => c * (n + 1)) ∧ ∀ x t, M.tm.spaceUsed (M.tm.initCfg x) t ≤ c` | `f2_idTM` | 0 | 1 / 1 | Inclusions 1 | 0 |
| Catalog:4269 | `computesFunInTime_const_spaceUsed` | `∃ (M : FinTM Bool) (c : ℕ), M.ComputesFunInTime (fun _ => w) (fun n => c * (n + 1)) ∧ ∀ x t, M.tm.spaceUsed (M.tm.initCfg x) t ≤ c` | `f2_constTM` | 5 | 0 / 0 | — | 0 |
| Catalog:4294 | `computesFunInTime_prepend_spaceUsed` | `∃ (M : FinTM Bool) (c : ℕ), M.ComputesFunInTime (fun x => w ++ x) (fun n => c * (n + 1)) ∧ ∀ x t, M.tm.spaceUsed (M.tm.initCfg x) t ≤ c` | `f2_catalogPrefixTM` | 1 | 1 / 1 | Constructible 1 | 0 |
| Catalog:4318 | `computesFunInTime_lengthBits_spaceUsed` | `∃ (M : FinTM Bool) (c : ℕ), M.ComputesFunInTime (fun x => Nat.bits x.length) (fun n => c * (n + 1)) ∧ ∀ x t, M.tm.spaceUsed (M.tm.initCfg…` | `f2_counterTM` | 1 | 2 / 1 | Constructible 2 | 1 |
| Catalog:4335 | `computesFunInTime_polyUnary_spaceUsed` | `∃ (M : FinTM Bool) (c : ℕ), M.ComputesFunInTime (fun x => List.replicate (C * (x.length + 1) ^ e) true) (fun n => c * (n + 1) ^ (e + 1)) …` | const row / `f2_catalogPolyUnaryTM` | 0 | 1 / 1 | Inclusions 1 | 1 |
| Catalog:4377 | `computesFunInTime_polyBits_spaceUsed` | `∃ (M : FinTM Bool) (c : ℕ), M.ComputesFunInTime (fun x => Nat.bits (C * (x.length + 1) ^ e)) (fun n => c * (n + 1) ^ (e + 1)) ∧ ∀ x t, M.…` | const row / `bufferedCompTM f2_catalogPolyUnaryTM f2_counterTM` | 0 | 0 / 0 | — | 0 |
| Catalog:4447 | `computesFunInTime_pairEncodeFixed_spaceUsed` | `∃ (M : FinTM Bool) (c : ℕ), M.ComputesFunInTime (fun x => pairEncode α x) (fun n => c * (n + 1)) ∧ ∀ x t, M.tm.spaceUsed (M.tm.initCfg x)…` | the prepend space row | 0 | 0 / 0 | — | 0 |
| Catalog:4465 | `computesFunInTime_pairFst_spaceUsed` | `∃ (M : FinTM Bool) (c : ℕ), M.ComputesFunInTime (fun x => ((pairDecode x).map Prod.fst).getD []) (fun n => c * (n + 1)) ∧ ∀ x t, M.tm.spa…` | `f2_pairExtractTM` | 0 | 0 / 0 | — | 0 |
| Catalog:4490 | `computesFunInTime_pairSnd_spaceUsed` | `∃ (M : FinTM Bool) (c : ℕ), M.ComputesFunInTime (fun x => ((pairDecode x).map Prod.snd).getD []) (fun n => c * (n + 1)) ∧ ∀ x t, M.tm.spa…` | `f2_pairExtractTM` | 1 | 0 / 0 | — | 0 |
| Catalog:4515 | `computesFunInTime_pairValid_spaceUsed` | `∃ (M : FinTM Bool) (c : ℕ), M.ComputesFunInTime (fun x => [(pairDecode x).isSome]) (fun n => c * (n + 1)) ∧ ∀ x t, M.tm.spaceUsed (M.tm.i…` | `f2_pairValidTM` | 0 | 0 / 0 | — | 0 |
| Catalog:4535 | `computesFunInTime_pairConcat_spaceUsed` | `∃ (M : FinTM Bool) (c : ℕ), M.ComputesFunInTime (fun z => match pairDecode z with \| some (a, b) => a ++ b \| none => []) (fun n => c * (n …` | `f2_pairExtractTM` | 0 | 0 / 0 | — | 0 |
| Catalog:4563 | `computesFunInTime_pairDup_spaceUsed` | `∃ (M : FinTM Bool) (c : ℕ), M.ComputesFunInTime (fun x => pairEncode x x) (fun n => c * (n + 1)) ∧ ∀ x t, M.tm.spaceUsed (M.tm.initCfg x)…` | `f2_pairDupTM` | 0 | 0 / 0 | — | 0 |
| Catalog:4615 | `computesFunInTime_pairLenCheck_spaceUsed` | `∃ (M : FinTM Bool) (c : ℕ), M.ComputesFunInTime (fun x => [match pairDecode x with \| some (a, b) => decide (b.length ≤ C * (a.length + 1)…` | `f2_pairCountTM` over a buffered composite | 0 | 0 / 0 | — | 0 |
| Catalog:5049 | `computesFunInTime_stripLast_spaceUsed` | `∃ (M : FinTM Bool) (c : ℕ), M.ComputesFunInTime (fun x => match pairDecode x with \| some (a, v) => match splitAtLastTrue v with \| some u …` | existential (`f2_strip_linear`, through `computesFunInTime_cond`) | 0 | 0 / 0 | — | 0 |
| Catalog:5087 | `computesFunInTime_incFixed_spaceUsed` | `∃ (M : FinTM Bool) (c : ℕ), M.ComputesFunInTime (fun x => (incFixed x).getD []) (fun n => c * (n + 1)) ∧ ∀ x t, M.tm.spaceUsed (M.tm.init…` | `f2_incFixedTM` | 0 | 0 / 0 | — | 0 |
| Catalog:5901 | `computesFunInTime_pairMapSnd_spaceUsed` | `∃ (M : FinTM Bool) (c : ℕ), M.ComputesFunInTime (fun z => match pairDecode z with \| some (a, b) => pairEncode a (g b) \| none => []) (fun …` | `a2_mapTM Mg true` (new, not a copy) | 0 | 0 / 0 | — | 0 |
| Catalog:9993 | `computesFunInTime_splitSolve_spaceUsed` | `∃ (M : FinTM Bool) (c : ℕ), M.ComputesFunInTime (fun w => match solveSplit C e w.length with \| some i => pairEncode (w.take i) (w.drop i)…` | `f2_splitSolve_closed` (`f2_loopHost` over `f2_splitBodyTM`) | 0 | 0 / 0 | — | 0 |
| Catalog:10693 | `computesFunInTime_cond_spaceUsed` | `∃ (M : FinTM Bool) (c : ℕ), M.ComputesFunInTime (fun x => if p x then f₁ x else f₂ x) (fun n => c * (T₀ n + max (T₁ n) (T₂ n) + 1)) ∧ ∀ x…` | `f2_timedCondTM` | 0 | 0 / 0 | — | 0 |
| Catalog:11209 | `exists_loopTM_spaceUsed` | `∃ (E : FinTM Bool) (c : ℕ), E.ComputesFunInTime (fun x => [(List.range (R x.length + 1)).any fun i => acceptF x ((stepF x)^[i] (s0 x))]) …` | `f2_loopHost` | 0 | 0 / 0 | — | 0 |
| Primitives:2096 | `computesFunInTime_prepend` | `∃ (M : FinTM Bool) (c : ℕ), M.ComputesFunInTime (fun x => w ++ x) fun n => c * (n + 1)` | `catalogPrefixTM` (P, Primitives:129) | 1 | 4 / 4 | NP 1, PolyTimePairing 1, SAT 1, CodeSimulator 1 | 1 |
| Primitives:2111 | `computesFunInTime_lengthBits` | `∃ (M : FinTM Bool) (c : ℕ), M.ComputesFunInTime (fun x => Nat.bits x.length) fun n => c * (n + 1)` | `Complexity.counterTM` (P, TimeConstructible:130), through `timeConstructible_id` | 4 | 10 / 6 | MeyerVerifierGlue 1, Nondeterminism 2, SAT 1, TMSAT 1, Hardness 4, CodeSimulator 1 | 1 |
| Primitives:2133 | `computesFunInTime_polyUnary` | `∃ (M : FinTM Bool) (c : ℕ), M.ComputesFunInTime (fun x => List.replicate (C * (x.length + 1) ^ e) true) fun n => c * (n + 1) ^ (e + 1)` | `constTM` / `catalogPolyUnaryTM` (P, Primitives:1009), split on `e` | 2 | 12 / 7 | EXP 3, NP 1, Nondeterminism 3, PolyTimePairing 2, TMSAT 1, Hardness 1, Padding 1 | 2 |
| Primitives:2157 | `computesFunInTime_polyBits` | `∃ (M : FinTM Bool) (c : ℕ), M.ComputesFunInTime (fun x => Nat.bits (C * (x.length + 1) ^ e)) fun n => c * (n + 1) ^ (e + 1)` | existential composite (`computesFunInTime_comp` of two rows) | 0 | 1 / 1 | EmitIterBody 1 | 3 |
| Primitives:2194 | `computesFunInTime_pairEncodeFixed` | `∃ (M : FinTM Bool) (c : ℕ), M.ComputesFunInTime (fun x => pairEncode α x) fun n => c * (n + 1)` | the prepend row at a fixed word | 0 | 3 / 2 | TMSAT 1, Hardness 2 | 1 |
| Primitives:2209 | `computesFunInTime_pairFst` | `∃ (M : FinTM Bool) (c : ℕ), M.ComputesFunInTime (fun x => ((pairDecode x).map Prod.fst).getD []) fun n => c * (n + 1)` | `pairExtractTM true false` (P, Primitives:665) | 1 | 13 / 9 | Advice 1, PPolyAdvice 1, EXP 1, Nondeterminism 2, PolyTimePairing 2, SAT 2, Hardness 2, CertShell 1, CodeSimulator 1 | 3 |
| Primitives:2228 | `computesFunInTime_pairSnd` | `∃ (M : FinTM Bool) (c : ℕ), M.ComputesFunInTime (fun x => ((pairDecode x).map Prod.snd).getD []) fun n => c * (n + 1)` | `pairExtractTM false true` | 1 | 12 / 7 | PPolyAdvice 1, Nondeterminism 2, PolyTimePairing 3, SAT 2, TMSAT 1, Hardness 2, CertShell 1 | 3 |
| Primitives:2245 | `computesFunInTime_pairValid` | `∃ (M : FinTM Bool) (c : ℕ), M.ComputesFunInTime (fun x => [(pairDecode x).isSome]) fun n => c * (n + 1)` | `pairValidTM` (P, Primitives:569) | 0 | 9 / 7 | NP 2, Nondeterminism 1, SAT 1, TMSAT 2, EXPCOM 1, Padding 1, CodeSimulator 1 | 1 |
| Primitives:2261 | `computesFunInTime_pairConcat` | `∃ (M : FinTM Bool) (c : ℕ), M.ComputesFunInTime (fun z => match pairDecode z with \| some (a, b) => a ++ b \| none => []) fun n => c * (n + 1)` | `pairExtractTM true true` | 0 | 10 / 6 | NP 1, Nondeterminism 2, PolyTimePairing 3, SAT 1, TMSAT 1, Hardness 2 | 3 |
| Primitives:2282 | `computesFunInTime_pairDup` | `∃ (M : FinTM Bool) (c : ℕ), M.ComputesFunInTime (fun x => pairEncode x x) fun n => c * (n + 1)` | `pairDupTM` (P, Primitives:271) | 0 | 5 / 4 | Advice 1, Nondeterminism 2, PolyTimePairing 1, Hardness 1 | 3 |
| Primitives:2715 | `computesFunInTime_pairMapSnd` | `∃ (M : FinTM Bool) (c : ℕ), M.ComputesFunInTime (fun z => match pairDecode z with \| some (a, b) => pairEncode a (g b) \| none => []) fun n…` | `pairMapTM (bufferedCompTM (pairExtractTM false true) Mg)` (P, Primitives:2297) | 0 | 6 / 5 | Advice 1, Nondeterminism 2, PolyTimePairing 1, SAT 1, Hardness 1 | 3 |
| Primitives:2751 | `computesFunInTime_pairLenCheck` | `∃ (M : FinTM Bool) (c : ℕ), M.ComputesFunInTime (fun x => [match pairDecode x with \| some (a, b) => decide (b.length ≤ C * (a.length + 1)…` | `pairCountTM G` (P, Primitives:1417), `G` an existential composite | 0 | 2 / 2 | NP 1, PolyTimePairing 1 | 1 |
| Primitives:2812 | `computesFunInTime_stripLast` | `∃ (M : FinTM Bool) (c : ℕ), M.ComputesFunInTime (fun x => match pairDecode x with \| some (a, v) => match splitAtLastTrue v with \| some u …` | existential (`computesFunInTime_cond` over `rawStripTM`, `anyTrueTM`) | 0 | 6 / 5 | PPolyAdvice 2, NP 1, PolyTimePairing 1, Hardness 1, Padding 1 | 3 |
| Primitives:4302 | `computesFunInTime_splitSolve` | `∃ (M : FinTM Bool) (c : ℕ), M.ComputesFunInTime (fun w => match solveSplit C e w.length with \| some i => pairEncode (w.take i) (w.drop i)…` | `splitSolve_closed` (P): `exists_loopFindTM` over `splitBodyTM` | 0 | 8 / 8 | MeyerSigmaEXP 1, NP 1, Nondeterminism 1, SAT 1, TMSAT 1, Tautology 1, Levels 1, CertShell 1 | 4 |
| Primitives:4323 | `computesFunInTime_incFixed` | `∃ (M : FinTM Bool) (c : ℕ), M.ComputesFunInTime (fun x => (incFixed x).getD []) fun n => c * (n + 1)` | `incFixedTM` (P, Primitives:460) | 0 | 6 / 6 | MeyerVerifierGlue 1, EXP 1, Nondeterminism 1, TMSAT 1, EXPCOM 1, CodeSimulator 1 | 2 |
| Primitives:6072 | `computesFunInTime_splitSolveWith` | `∃ (M : FinTM Bool) (c : ℕ), M.ComputesFunInTime (fun w => match solveSplitWith f w.length with \| some i => pairEncode (w.take i) (w.drop …` | `emitterP2_closed` (P): two `exists_installCallTM`, a loop | 0 | 2 / 2 | EXP 1, Nondeterminism 1 | 2 |
| Primitives:6226 | `computesFunInTime_unaryToken` | `∃ (M : FinTM Bool) (c : ℕ), M.ComputesFunInTime (fun x => pairEncode (unaryTokenSplit x).1 (unaryTokenSplit x).2) fun n => c * (n + 1)` | `emitterTokenTM` (P, Primitives:6087) | 0 | 1 / 1 | SAT 1 | 0 |
| Primitives:6295 | `computesFunInTime_appendBit` | `∃ (M : FinTM Bool) (c : ℕ), M.ComputesFunInTime (fun x => x ++ [b]) fun n => c * (n + 1)` | `emitterAppendTM b` (P, Primitives:6252) | 0 | 2 / 2 | EXPCOM 1, CodeSimulator 1 | 0 |
| Composition:137 | `computesFunInTime_id` | `∃ (M : FinTM Bool) (c : ℕ), M.ComputesFunInTime id fun n => c * (n + 1)` | `idTM` (P, Composition:88) | 0 | 1 / 1 | PolyTime 1 | 4 |
| Composition:179 | `computesFunInTime_const` | `∃ (M : FinTM Bool) (c : ℕ), M.ComputesFunInTime (fun _ => w) fun n => c * (n + 1)` | `constTM` (P, Composition:168) | 0 | 29 / 11 | Advice 1, CircuitSatReduction 1, EXP 1, Nondeterminism 2, PolyTimePairing 1, TMSAT 1, Tautology 1, Hardness 17, Primitives 2, CodeSimulator 1, Halting 1 | 4 |
| Composition:335 | `computesFunInTime_ifEq` | `∃ (M : FinTM Bool) (c : ℕ), M.ComputesFunInTime (fun w => if w = w₀ then u else v) fun n => c * (n + 1)` | `ifEqTM` (P, Composition:189) | 0 | 9 / 9 | CircuitSatReductionValid 1, MeyerSigmaEXP 1, CoNP 1, Nondeterminism 1, SAT 1, TMSAT 1, Hardness 1, EXPCOM 1, Halting 1 | 5 |
| Composition:391 | `computesFunInTime_comp` | `∃ (M : FinTM Bool) (c : ℕ), M.ComputesFunInTime (g ∘ f) fun n => c * (T₁ n + T₂ (T₁ n) + 1)` | `bufferedCompTM` (public, Simulation:618) | 0 | 14 / 9 | MeyerSigmaEXP 2, CoNP 1, EXP 1, Nondeterminism 1, PolyTime 1, TMSAT 1, Catalog 1, Primitives 3, CodeSimulator 3 | 6 |
| Composition:415 | `exists_comp_on_image` | `∃ N : FinTM Bool, N.ComputesFunInTime g (fun n => 2 * T₁ n + T₂ n + 2)` | `bufferedCompTM` (public) | 0 | 5 / 3 | SAT 2, TMSAT 2, EXPCOM 1 | 1 |
| Composition:474 | `exists_comp_partial` | `∃ M : FinTM Bool, ∀ x w : List Bool, (∃ t, M.ComputesInTime x w t) ↔ ∃ y : List Bool, (∃ t, M₁.ComputesInTime x y t) ∧ ∃ t, M₂.ComputesIn…` | `bufferedCompTM` (public) | 0 | 7 / 3 | UHaltMachine 1, NotTimeConstructible 3, Halting 3 | 9 |
| Composition:654 | `exists_cond` | `∃ M : FinTM Bool, ∀ x w : List Bool, (∃ t, M.ComputesInTime x w t) ↔ ∃ t, (cond (p x) M₁ M₂).ComputesInTime x w t` | `condTM` (P, Composition:517) | 0 | 2 / 2 | NotTimeConstructible 1, Halting 1 | 6 |
| Loop:2243 | `exists_loopCfgTM` | `∃ (E : FinTM Bool) (c : ℕ), ∀ x : List Bool, ∃ (cfg : ℕ → Cfg E.k Bool E.State x) (startup : ℕ), startup ≤ c * (T x.length + 1) ∧ E.tm.ru…` | `loopHost _ _ _ false` (P abbrev, Loop:649) | 1 | 1 / 1 | EXP 1 | 4 |
| Loop:2370 | `exists_loopTM` | `∃ (E : FinTM Bool) (c : ℕ), E.ComputesFunInTime (fun x => [(List.range (R x.length + 1)).any fun i => acceptF x ((stepF x)^[i] (s0 x))]) …` | through `exists_loopCfgTM` (`loopHost`) | 0 | 0 / 0 | — | 2 |
| Loop:2484 | `exists_loopFindTM` | `∃ (E : FinTM Bool) (c : ℕ), E.ComputesFunInTime (fun x => match (List.range (R x.length + 1)).find? (fun i => acceptF x ((stepF x)^[i] (s…` | `loopHost _ _ _ true` | 0 | 3 / 2 | Nondeterminism 1, Primitives 2 | 6 |
| Loop:4775 | `exists_emitLoopTM` | `∃ (E : FinTM Bool) (c : ℕ), E.ComputesFunInTime (fun x => (List.range (R x.length + 1)).flatMap (fun i => emitF x ((stepF x)^[i] (s0 x)))…` | `emLoopHost` (P abbrev, Loop:4623) | 0 | 4 / 4 | SAT 1, Tautology 1, Hardness 1, EmitIterBody 1 | 10 |
| Loop:4912 | `exists_installCallTM` | `∃ (C : FinTM Bool) (entry exit : C.State) (c : ℕ), 0 < C.k ∧ ∀ (x arg : List Bool), ∃ t ≤ c * (T arg.length + arg.length + (f arg).length…` | `emCallTM M false`, `q₀`, `.inr (.inr 5)` (P, Loop:3897) | 0 | 12 / 9 | EXP 1, SAT 1, Hardness 2, CertShell 2, EmitIterBody 1, InputCall 1, OracleSim 1, Primitives 2, CodeSimulator 1 | 13 |
| Loop:4958 | `exists_emitCallTM` | `∃ (C : FinTM Bool) (entry exit : C.State) (c : ℕ), 0 < C.k ∧ ∀ (x arg : List Bool), ∃ t ≤ c * (T arg.length + arg.length + (f arg).length…` | `emCallTM M true`, same states | 0 | 3 / 3 | SAT 1, Hardness 1, EmitIterBody 1 | 9 |
| Wrappers:711 | `computesFunInTime_cond` | `∃ (M : FinTM Bool) (c : ℕ), M.ComputesFunInTime (fun x => if p x then f₁ x else f₂ x) (fun n => c * (T₀ n + max (T₁ n) (T₂ n) + 1))` | `timedCondTM` (P, Wrappers:479) | 0 | 7 / 7 | CircuitSatReduction 1, Nondeterminism 1, PolyTimePairing 1, Hardness 1, Catalog 1, Primitives 1, CodeSimulator 1 | 4 |
| Encoding:491 | `computesFunInTime_pairEncode_diag` | `∃ (M : FinTM Bool) (c : ℕ), M.ComputesFunInTime (fun α => pairEncode α α) fun n => c * (n + 1)` | `pairDiagTM` (P, Encoding:299) | 0 | 1 / 1 | Halting 1 | 1 |
| Encoding:609 | `exists_codeTM` | `∃ M' : CodeTM, ∀ (x output : List Bool) (t : ℕ), M'.toFinTM.ComputesInTime x output t ↔ M.ComputesInTime x output t` | anonymous `⟨card Q − 1, tm.relabelState e⟩` | 0 | 6 / 6 | Reductions 1, TMSAT 1, EXPCOM 1, Diagonal 1, Universal 1, Diagonalization 1 | 9 |

Totals: the 53 rows have **221 external code citations in 35 distinct files**; the 34 home rows
have 216 in 33 files. Sixteen rows have no external code citation: 15 Catalog space rows
(all but `id`, `prepend`, `lengthBits` and `polyUnary`) and `exists_loopTM`.

Two of the rows today use witnesses that compute the same function as another row's witness:
`computesFunInTime_pairDup` (Primitives, `pairDupTM`, no work tapes) and
`Turing.computesFunInTime_pairEncode_diag` (Encoding, `pairDiagTM`, no work tapes) both compute
`x ↦ pairEncode x x` in linear time. And `computesFunInTime_pairMapSnd` uses the captured-payload
`pairMapTM`, while its Catalog space row uses a different machine, the forwarding controller
`a2_mapTM Mg true`, because the captured payload visits `|g b| + 1` capture cells (the F2 gate's
round-1 finding 4, quoted in the space row's docstring, Catalog:5885–5888).

## 2. The `f2_` region of `Build/Catalog.lean`

### 2.1 Layout

Catalog has 12,752 lines. Its three parts: Part 1 (lines 147–1777, namespace `Turing`: the R3
machines, the framed rows, the canonical rows); the region (1779–11361, namespace
`Turing.FinTM`); Part 3 (11371–12752, the §12.8 rows). The region, by category
(`decls.py`, `verbatim.py`; lines with docstrings):

| Category | Declarations | Lines |
|---|---|---|
| `f2_` copies with a same-named source in a home file | 257 | 5,606 |
| `f2_` declarations with no same-named source (new space proofs and glue) | 47 | 1,323 |
| `a2_` declarations (new: the forwarding map controller, 30; the loop head ledger, 15) | 45 | 1,196 |
| `catalog_redirect*` (copies of Wrappers' private `redirectState`/`Action`/`Cfg`/`_run` family) | 7 | 77 |
| Public declarations (§2.2) | 22 | 992 |
| Blank lines and section comments between declarations | — | 389 |
| **Region** | **378** | **9,583** |

Sources of the 257 named copies: Primitives 145, Loop 80, TimeConstructible 19, Wrappers 10,
Composition 3. The 25 that differ from their source are the loop-host family copied from an
older `Build/Loop.lean` (21: `f2_loopHost` and its phase lemmas; Loop has since generalized
`loopHost` to `loopHostM … forward findMode`, Loop:576–650) and four split-search lemmas
(`f2_splitBody_round`, `f2_splitSolve_of_body`, `_source`, `_closed`), changed to thread space.

No region declaration uses a public Catalog declaration from outside the region
(`deps.py`); inside it, the rows use `computesFunInTime_const_spaceUsed`,
`computesFunInTime_prepend_spaceUsed`, `computesFunInTime_pairSnd_spaceUsed`,
`computesFunInTime_lengthBits_spaceUsed`, `rewind_heads` and `rewind_scan_heads`.

### 2.2 The 22 public declarations of the region

| Line | Name | Kind | Lines | Internal | External | External files |
|---|---|---|---|---|---|---|
| 4226 | `computesFunInTime_id_spaceUsed` | existential space row | 44 | 0 | 1 | Inclusions 1 |
| 4269 | `computesFunInTime_const_spaceUsed` | existential space row | 21 | 5 | 0 | — |
| 4294 | `computesFunInTime_prepend_spaceUsed` | existential space row | 22 | 1 | 1 | Constructible 1 |
| 4318 | `computesFunInTime_lengthBits_spaceUsed` | existential space row | 17 | 1 | 2 | Constructible 2 |
| 4335 | `computesFunInTime_polyUnary_spaceUsed` | existential space row | 32 | 0 | 1 | Inclusions 1 |
| 4377 | `computesFunInTime_polyBits_spaceUsed` | existential space row | 79 | 0 | 0 | — |
| 4447 | `computesFunInTime_pairEncodeFixed_spaceUsed` | existential space row | 16 | 0 | 0 | — |
| 4465 | `computesFunInTime_pairFst_spaceUsed` | existential space row | 26 | 0 | 0 | — |
| 4490 | `computesFunInTime_pairSnd_spaceUsed` | existential space row | 24 | 1 | 0 | — |
| 4515 | `computesFunInTime_pairValid_spaceUsed` | existential space row | 19 | 0 | 0 | — |
| 4535 | `computesFunInTime_pairConcat_spaceUsed` | existential space row | 27 | 0 | 0 | — |
| 4563 | `computesFunInTime_pairDup_spaceUsed` | existential space row | 17 | 0 | 0 | — |
| 4615 | `computesFunInTime_pairLenCheck_spaceUsed` | existential space row | 86 | 0 | 0 | — |
| 5049 | `computesFunInTime_stripLast_spaceUsed` | existential space row | 42 | 0 | 0 | — |
| 5087 | `computesFunInTime_incFixed_spaceUsed` | existential space row | 18 | 0 | 0 | — |
| 5901 | `computesFunInTime_pairMapSnd_spaceUsed` | existential space row | 166 | 0 | 0 | — |
| 9993 | `computesFunInTime_splitSolve_spaceUsed` | existential space row | 25 | 0 | 0 | — |
| 10101 | `redirectTM_spaceUsedByTape` | space row on the public `redirectTM` | 22 | 0 | 0 | — |
| 10376 | `rewind_scan_heads` | head lemma (Simulation's rewind) | 36 | 1 | 0 | — |
| 10415 | `rewind_heads` | head lemma (Simulation's rewind) | 34 | 2 | 3 | Inclusions 1, InputCall 1, InputLength 1 |
| 10693 | `computesFunInTime_cond_spaceUsed` | existential space row | 42 | 0 | 0 | — |
| 11209 | `exists_loopTM_spaceUsed` | existential space row | 177 | 0 | 0 | — |

Space statements of Catalog outside the region: `capture_visitedByTapeHead` (1725, W1, no
external consumer) and `transferTM_`, `copyTM_`, `clearTM_`, `compareTM_`,
`incrementTM_spaceUsedByTape` (1344–1685, 181 lines, no external consumer).

### 2.3 Every `f2_` declaration, grouped by the row it re-derives

Grouping (`group.py`): each `f2_` declaration is assigned to the public row of the region with
the smallest dependency closure that reaches it (closures over identifier occurrences,
`deps.py`); "also used by" counts the members reached from other rows as well. Tags: no tag =
code-identical to the same-named source after removing the prefix; `(≈)` = same-named source,
modified; `(new)` = no same-named source. The number after each name is its line.

#### computesFunInTime_id_spaceUsed: 2 declarations, 46 lines with docstrings

Re-derives the witness of `computesFunInTime_id`. Copies: 2 identical, 0 modified, 0 with no
same-named source.

`f2_idTM` 1787, `f2_idTM_run` 1799

#### computesFunInTime_const_spaceUsed: 1 declaration, 5 lines with docstrings

Re-derives the witness of `computesFunInTime_const`. Copies: 1 identical, 0 modified, 0 with no
same-named source.

`f2_constTM` 1834

#### computesFunInTime_prepend_spaceUsed: 5 declarations, 77 lines with docstrings

Re-derives the witness of `computesFunInTime_prepend (and pairEncodeFixed)`. Copies: 5 identical, 0
modified, 0 with no same-named source. Also used by: `computesFunInTime_splitSolve_spaceUsed` (3).

`f2_catalogPrefixTM` 1841, `f2_catalogPrefixCfg` 1854, `f2_catalogPrefixTM_emit` 1860,
`f2_catalogPrefixTM_copy` 1879, `f2_catalogPrefixTM_computes` 1910

#### computesFunInTime_incFixed_spaceUsed: 7 declarations, 191 lines with docstrings

Re-derives the witness of `computesFunInTime_incFixed`. Copies: 7 identical, 0 modified, 0 with no
same-named source. Also used by: `computesFunInTime_pairConcat_spaceUsed` (2),
`computesFunInTime_pairDup_spaceUsed` (2), `computesFunInTime_pairFst_spaceUsed` (2),
`computesFunInTime_pairLenCheck_spaceUsed` (2), `computesFunInTime_pairSnd_spaceUsed` (2),
`computesFunInTime_pairValid_spaceUsed` (2), `computesFunInTime_stripLast_spaceUsed` (2).

`f2_scanCfg` 1923, `f2_scanCfg_read` 1928, `f2_scanCopy_suffix` 2085, `f2_scanTrues_run` 2124,
`f2_incFixed_cases` 2154, `f2_incFixedTM` 2172, `f2_incFixed_computes` 2199

#### computesFunInTime_pairDup_spaceUsed: 5 declarations, 138 lines with docstrings

Re-derives the witness of `computesFunInTime_pairDup`. Copies: 5 identical, 0 modified, 0 with no
same-named source.

`f2_scanCopy_run` 1942, `f2_scanCopy_finish` 1966, `f2_pairDupTM` 1983, `f2_pairDup_double` 2005,
`f2_pairDup_computes` 2043

#### computesFunInTime_pairValid_spaceUsed: 5 declarations, 106 lines with docstrings

Re-derives the witness of `computesFunInTime_pairValid`. Copies: 5 identical, 0 modified, 0 with no
same-named source. Also used by: `computesFunInTime_stripLast_spaceUsed` (1).

`f2_scanStep_right` 2265, `f2_pairValidTM` 2281, `f2_pairValid_block` 2294, `f2_pairValid_run` 2319,
`f2_pairValid_computes` 2363

#### computesFunInTime_pairConcat_spaceUsed: 13 declarations, 334 lines with docstrings

Re-derives the witness of `computesFunInTime_pairFst, pairSnd, pairConcat`. Copies: 12 identical, 0
modified, 1 with no same-named source. Also used by: `computesFunInTime_pairFst_spaceUsed` (13),
`computesFunInTime_pairLenCheck_spaceUsed` (13), `computesFunInTime_pairSnd_spaceUsed` (13),
`computesFunInTime_polyBits_spaceUsed` (1), `computesFunInTime_stripLast_spaceUsed` (1).

`f2_pairExtractTM` 2378, `f2_extractCfg` 2407, `f2_extractCfg_read` 2413, `f2_extract_first` 2419,
`f2_extract_block` 2435, `f2_extract_rewind` 2463, `f2_extract_replay` 2497,
`f2_extract_replay_finish` 2524, `f2_extract_suffix` 2541, `f2_extract_finish` 2585,
`f2_extract_run` 2615, `f2_pairExtract_computes` 2673, `f2_space_of_time` 4192 (new)

#### computesFunInTime_polyUnary_spaceUsed: 23 declarations, 608 lines with docstrings

Re-derives the witness of `computesFunInTime_polyUnary (and polyBits)`. Copies: 18 identical, 0
modified, 5 with no same-named source. Also used by: `computesFunInTime_lengthBits_spaceUsed` (1),
`computesFunInTime_pairLenCheck_spaceUsed` (18), `computesFunInTime_pairMapSnd_spaceUsed` (1),
`computesFunInTime_polyBits_spaceUsed` (18), `computesFunInTime_splitSolve_spaceUsed` (14),
`exists_loopTM_spaceUsed` (1).

`f2_CatalogPolyControl` 2693, `f2_catalogPolyTape` 2709, `f2_catalogPolyMove` 2713,
`f2_catalogPolyUnaryTM` 2720, `f2_catalogPolyCfg` 2750, `f2_catalogPolyMove_apply` 2756,
`f2_catalogPoly_emit` 2770, `f2_catalogPoly_rewind` 2792, `f2_catalogPoly_advance` 2825,
`f2_catalogPolyCost` 2835, `f2_catalogPoly_loop` 2847, `f2_catalogPolyTape_write` 2952,
`f2_catalogPolyCost_le` 2965, `f2_catalogPolyCopyCfg` 2984, `f2_catalogPoly_copy` 2989,
`f2_catalogPoly_setup` 3024, `f2_catalogPoly_start` 3048, `f2_catalogPoly_unary_computes` 3082,
`f2_polyHeads` 3122 (new), `f2_polyHeads_bounds` 3132 (new), `f2_poly_step` 3147 (new),
`f2_head_steps` 3270 (new), `f2_poly_space` 3288 (new)

#### Not reached from any public row: 17 declarations, 270 lines with docstrings

Four are instances (`…Fintype`, `…DecidableEq`), which the text scan cannot follow and which are
used implicitly; the other 13 are not reached from any public declaration of Catalog (dead in the
copy region). Copies: 6 identical, 0 modified, 11 with no same-named source.

`f2_catalogPolyControlFintype` 2701, `f2_catalogPolyControlDecidableEq` 2705,
`f2_loop_silent_prefix` 6058 (new), `f2_loopDebitTM` 6308 (new), `f2_loopDebitCfg` 6324 (new),
`f2_loopBorrow_step` 6331 (new), `f2_loopBorrow_run` 6357 (new), `f2_loopBorrow_rewind` 6382 (new),
`f2_loopBorrow_correct` 6416 (new), `f2_loopBody_capture` 6562 (new), `f2_splitFind_none` 8562
(new), `f2_catalogFirstEntry` 8955, `f2_splitRestore_first` 8974, `f2_splitCount_firstHalt` 9017
(new), `f2_splitPrepare_first` 9162 (new), `f2_splitBodyStateFintype` 9292,
`f2_splitBodyStateDecidableEq` 9297

#### computesFunInTime_lengthBits_spaceUsed: 23 declarations, 458 lines with docstrings

Re-derives the witness of `computesFunInTime_lengthBits / Complexity.timeConstructible_id`. Copies:
19 identical, 0 modified, 4 with no same-named source. Also used by:
`computesFunInTime_polyBits_spaceUsed` (20).

`f2_counterInc` 3334, `f2_counterCarry` 3340, `f2_counterInc_potential` 3346, `f2_counterInc_bits`
3358, `f2_counterInc_length` 3374, `f2_counterBump` 3383, `f2_counterTM` 3390, `f2_counterTape`
3411, `f2_counterCfg` 3415, `f2_counterTape_read` 3420, `f2_counterTape_write` 3430,
`f2_counter_carry_step` 3451, `f2_counter_carry` 3476, `f2_counter_rewind` 3507, `f2_counter_start`
3542, `f2_counter_increment` 3571, `f2_counter_count` 3593, `f2_counter_emit_run` 3622,
`f2_counter_emit` 3650, `f2_counter_computes` 3671 (new), `f2_counter_count_space` 3704 (new),
`f2_counter_heads` 3755 (new), `f2_counter_space` 3799 (new)

#### computesFunInTime_pairLenCheck_spaceUsed: 14 declarations, 366 lines with docstrings

Re-derives the witness of `computesFunInTime_pairLenCheck`. Copies: 12 identical, 0 modified, 2 with
no same-named source. Also used by: `computesFunInTime_splitSolve_spaceUsed` (1).

`f2_lenAction` 3816, `f2_pairCountTM` 3824, `f2_lenCfg` 3854, `f2_lenCfg_read` 3865,
`f2_lenAction_apply` 3872, `f2_lenSuffix_run` 3891, `f2_lenParse_first` 3947, `f2_lenParse_block`
3964, `f2_lenParse_run` 3997, `f2_catalogRewind` 4058, `f2_lenStart` 4088, `f2_pairCount_computes`
4145, `f2_unary_sharp` 4576 (new), `f2_first_length` 4595 (new)

#### computesFunInTime_stripLast_spaceUsed: 16 declarations, 353 lines with docstrings

Re-derives the witness of `computesFunInTime_stripLast`. Copies: 14 identical, 0 modified, 2 with no
same-named source. Also used by: `computesFunInTime_pairLenCheck_spaceUsed` (1).

`f2_catalogPair_inverse` 4166 (new), `f2_rawStripTM` 4693, `f2_stripCfg` 4713,
`f2_catalogBuffer_erase` 4718, `f2_rawStrip_copy` 4729, `f2_rawStrip_rewind` 4755,
`f2_rawStrip_replay` 4788, `f2_rawStrip_finish` 4810, `f2_rawStrip_erase` 4822, `f2_rawStrip_trim`
4841, `f2_rawStrip_computes` 4868, `f2_anyTrueTM` 4888, `f2_anyTrue_run` 4901, `f2_anyTrue_computes`
4934, `f2_catalogMarker_cases` 4950, `f2_strip_linear` 4971 (new)

#### exists_loopTM_spaceUsed: 87 declarations, 2014 lines with docstrings

Re-derives the witness of `exists_loopTM / exists_loopCfgTM / exists_loopFindTM (the loop host)`.
Copies: 58 identical, 21 modified, 8 with no same-named source. Also used by:
`computesFunInTime_splitSolve_spaceUsed` (87).

`f2_loop_live_prefix` 6047 (new), `f2_loop_first_halt` 6072, `f2_loop_orbit_inv` 6095,
`f2_loop_fuel_width` 6105, `f2_loop_input_move_le` 6112 (new), `f2_loop_input_run_le` 6126 (new),
`f2_loop_output_length_le` 6142, `f2_loop_rewind_bounded` 6159, `f2_loopDebit` 6191,
`f2_loopBorrowPos` 6197, `f2_loopBorrowPos_le` 6202, `f2_loopDebit_length` 6208, `f2_loopValue`
6214, `f2_loopValue_bits` 6219, `f2_loopDebit_value` 6230, `f2_loopDebit_success` 6244,
`f2_loopDebit_iterate_length` 6255, `f2_loopDebit_iterate_value` 6265, `f2_loopBuffer_read` 6279,
`f2_loopBuffer_write` 6287, `f2_loopBodyTM` 6434, `f2_loopBodyCfg` 6457, `f2_loopBody_stop` 6469,
`f2_loopBody_step` 6487, `f2_loopBody_run` 6534, `f2_LoopHostState` 6585, `f2_loopFuelSource` 6589,
`f2_loopBodySource` 6597, `f2_loopControlAction` 6604, `f2_loopHost` 6628 (≈),
`f2_loopHost_body_capture` 6705 (new), `f2_loopHost_fuel_capture` 6719 (≈), `f2_loopHost_init` 6731
(≈), `f2_loopControl_idle` 6740, `f2_loopHost_input_rewind` 6748 (≈), `f2_loopFrame` 6765,
`f2_loopWrite` 6785, `f2_loopControl_apply` 6792, `f2_loopReplayTM` 6828, `f2_loopReplayCfg` 6838,
`f2_loopReplay_step` 6844, `f2_loopReplay_run` 6868, `f2_loopControl_payload` 6884,
`f2_loopHost_replay` 6904, `f2_loopFuelCfg` 6941, `f2_loopFuel_run` 6950, `f2_loopFuel_init` 6963,
`f2_loopFrame_payload` 6980, `f2_loopFrame_counter` 6990, `f2_loopHost_fuel_rewind` 7002 (new),
`f2_loopCopyTape` 7052, `f2_loopCopy_read` 7056, `f2_loopCopy_erase` 7061, `f2_loopCopy_initial`
7074, `f2_loopCopy_final` 7082, `f2_loopHost_fuel_copy` 7096 (≈), `f2_loopHost_fuel_return` 7147
(≈), `f2_loopHost_fuel_setup` 7202 (≈), `f2_loopFuelCaptured` 7233, `f2_loopReady` 7240,
`f2_loopFuelCaptured_frame` 7252, `f2_loopHost_prepare` 7311 (≈), `f2_loopBodyPadded` 7358,
`f2_loopCall` 7368, `f2_loopBodySource_run` 7378, `f2_loopHost_anchor_return` 7393 (≈),
`f2_loopReady_call` 7434, `f2_loopHost_release` 7473 (≈), `f2_loopHost_start` 7506 (≈),
`f2_loopHost_halt_return` 7526 (≈), `f2_loopCall_frame` 7553 (≈), `f2_loopCall_reframe` 7580,
`f2_loopHost_borrow_step` 7612 (≈), `f2_loopHost_borrow_run` 7650 (≈), `f2_loopHost_borrow_rewind`
7683 (≈), `f2_loopHost_borrow` 7733 (≈), `f2_loopFrame_flag` 7755, `f2_loopFlag_clear` 7764,
`f2_loopHost_reject` 7775 (≈), `f2_loopHost_payload_rewind` 7847 (new), `f2_loopHost_frame_replay`
7900, `f2_loopHost_accept` 7935 (≈), `f2_loopHost_round` 8001 (≈), `f2_loopCall_heads` 8064 (new),
`f2_loopHost_bound` 8089, `f2_loopHost_contracts` 8113 (≈), `f2_space_radius` 8372 (new)

#### computesFunInTime_splitSolve_spaceUsed: 66 declarations, 1489 lines with docstrings

Re-derives the witness of `computesFunInTime_splitSolve`. Copies: 58 identical, 4 modified, 4 with
no same-named source.

`f2_loop_find_run` 8299, `f2_segment_heads` 8334 (new), `f2_seamed_space` 8390 (new),
`f2_exists_loopFind_space` 8411 (new), `f2_splitStep` 8512, `f2_splitAccept` 8516,
`f2_splitStep_inv` 8520, `f2_splitStep_orbit` 8528, `f2_catalogFind_congr` 8541, `f2_splitFind_eq`
8551, `f2_splitLoop_result` 8570, `f2_splitLoop_bound` 8590, `f2_splitPos` 8604, `f2_splitPos_read`
8608, `f2_splitPos_succ` 8619, `f2_splitScratch` 8634, `f2_splitScratch_erase` 8638,
`f2_splitRestoreTM` 8650, `f2_splitRestoreScan` 8672, `f2_splitRestore_scan` 8681,
`f2_splitRestoreClean` 8713, `f2_splitRestore_append` 8720, `f2_splitRestore_rewind` 8757,
`f2_splitRestore_run` 8790, `f2_splitCountAction` 8823, `f2_splitCountCfg` 8831,
`f2_splitCount_over` 8839, `f2_splitCount_apply` 8852, `f2_splitCount_run` 8883,
`f2_splitPoly_loop_end` 8928, `f2_splitCount_accept` 9002, `f2_splitPrepareTM` 9038,
`f2_splitPrepareScan` 9055, `f2_splitPrepare_scan` 9062, `f2_splitPrepareReady` 9089,
`f2_splitPrepare_extra` 9095, `f2_splitPrepare_rewind` 9114, `f2_splitPrepare_run` 9141,
`f2_splitSafe` 9182, `f2_splitSafe_add` 9187, `f2_splitEmbed_cut` 9204, `f2_splitRewindTM` 9251,
`f2_splitEmitTM` 9266, `f2_SplitBodyState` 9283, `f2_splitBodyTM` 9313, `f2_splitBank` 9336,
`f2_splitBody_start` 9342, `f2_splitEmbed_run` 9351 (new), `f2_splitBody_prepare` 9370,
`f2_splitBody_count` 9426, `f2_splitBody_rewind` 9457, `f2_splitBody_restore` 9484,
`f2_splitEmitCfg` 9509, `f2_splitEmit_double` 9519, `f2_splitEmit_separator` 9562,
`f2_splitEmit_suffix` 9586, `f2_splitEmit_run` 9627, `f2_splitSafe_one` 9644, `f2_splitSafe_join`
9656, `f2_splitBody_round` 9673 (≈), `f2_splitSolve_of_body` 9803 (≈), `f2_splitSource_poly` 9874,
`f2_splitSource_constant` 9884, `f2_splitBody_envelope` 9905, `f2_splitSolve_source` 9932 (≈),
`f2_splitSolve_closed` 9959 (≈)

#### computesFunInTime_cond_spaceUsed: 20 declarations, 474 lines with docstrings

Re-derives the witness of `computesFunInTime_cond`. Copies: 10 identical, 0 modified, 10 with no
same-named source.

`f2_timedPadTM` 10116, `f2_timedCondTM` 10125, `f2_timedBranchCfg` 10151, `f2_timedControlCfg`
10160, `f2_timed_capture` 10168, `f2_timed_control_init` 10185, `f2_timed_branch_run` 10206,
`f2_timedReadyCfg` 10241, `f2_timed_read` 10253, `f2_timed_start` 10311, `f2_cond_time` 10344 (new),
`f2_finSumEquiv` 10445 (new), `f2_sum_add` 10468 (new), `f2_branch_space` 10477 (new),
`f2_condHeads` 10518 (new), `f2_control_heads` 10525 (new), `f2_branch_heads` 10536 (new),
`f2_read_heads` 10544 (new), `f2_cond_ledger` 10570 (new), `f2_cond_space` 10633 (new)

Group totals: 304 declarations, 6,929 lines with docstrings. Every group's row is a space row;
the home row it re-derives is named in the group's first line.

### 2.4 The non-`f2_` private declarations of the region

* **`a2_` map controller, 30 declarations (5100–5841):** `a2_MapState`, `a2_mapStateFintype`,
  `a2_mapAct`, `a2_mapTM`, `a2_mapCfg`, `a2_mapVirtual` and 24 lemmas through `a2_map_space`;
  used only by `computesFunInTime_pairMapSnd_spaceUsed` (29 reached by text, the instance
  implicitly).
* **`a2_` loop head ledger, 15 declarations (10728–11150):** `a2_source_radius`, `a2_heads`,
  `a2_heads_mono`, `_steps`, `_join`, `_halted`, `a2_call_heads`, `a2_fuel_heads`,
  `a2_call_run`, `a2_call_prefix`, `a2_loop_prepare`, `a2_loop_start_prefix`, `a2_loop_round`,
  `a2_segments`, `a2_loop_halted_run`; used by `exists_loopTM_spaceUsed` (14; `a2_heads_halted`
  is not reached).
* **`catalog_redirect*`, 7 declarations (10008–10082):** `catalog_redirectState`,
  `catalog_redirectAction`, `catalog_redirectCfg`, `catalog_redirect_loop`, `_apply`, `_step`,
  `_run`; used only by `redirectTM_spaceUsedByTape`.

### 2.5 Dead declarations

Thirteen `f2_` declarations are reached from no public declaration of Catalog (§2.3, the
"not reached" group, less its four instances), and `a2_heads_halted` is not reached either.
Outside the region, `Primitives` has one private declaration reached from no public one
(`emitter_bits_injective`, 8 lines; `deps2.py`).

## 3. The R3 canonical `_run` rows

All six are derived from their framed `_run_ofCfg` forms (design §12.6) and specialize them to
`Cfg.ofWords` starts over `Bool`; each proof is a `Cfg.ext` computation of about 20 lines.

| Row | Line | Lines (with docstring) | External code citations |
|---|---|---|---|
| `transferTM_run` | 1297 | 49 | `Build/CertShell.lean:585`, `:589`, `:602` |
| `copyTM_run` | 1382 | 33 | `Build/CertShell.lean:571`; `TuringMachine/CodeSimulator.lean:1291` |
| `clearTM_run` | 1454 | 33 | none |
| `compareTM_run` | 1522 | 36 | none |
| `incrementTM_run_succ` | 1604 | 49 | none |
| `incrementTM_run_overflow` | 1651 | 37 | none |

Docstring mentions elsewhere: `Build/CertShell.lean:452` and `:706` (both name `copyTM_run` and
`transferTM_run`). `CertShell` belongs to W2-V, whose fill gate closed (wave 1);
`CodeSimulator` belongs to the B5a canonizer and H1 continuations, in flight. The framed forms
have their own consumers (`copyTM_run_ofCfg` 8 citations in 5 files, `clearTM_run_ofCfg` 4 in 4,
`incrementTM_run_succ_ofCfg` 4 in 4, `incrementTM_run_overflow_ofCfg` 3 in 3,
`compareTM_run_ofCfg` 1, `transferTM_run_ofCfg` none) and are not affected.

## 4. Other measured facts the design relies on

* **Imports** (`imports.py`). Catalog imports `Build/Loop` and `TuringMachine/Encoding`, not
  `Build/Primitives`; its import closure contains `Simulation`, `Composition`, `Wrappers`,
  `Encoding` and `Loop`, but neither Primitives nor TimeConstructible. Primitives does not import
  Catalog, so the edge Catalog → Primitives is acyclic. Of Catalog's 28 importers, 8 do not yet
  import Primitives (`Constructible`,
  `RecordTable`, `CounterLoop`, `Scan`, `Zone`, `InputCall`, `CfgRecord`, `InputLength`); the
  20 public names of Primitives and TimeConstructible would become visible there, and none of
  the 8 declares or uses any of them.
* **Replay closure.** The ten files MIG-1 edits (`Simulation`, `Composition`, `Wrappers`,
  `Encoding`, `TimeConstructible`, `Loop`, `Primitives`, `Catalog`, `CertShell`,
  `CodeSimulator`) and everything importing them: **205 of 623 modules** (61 in
  `CircuitComplexity`, 45 in `SpaceComplexity`, 45 in `TuringMachine`, 19 in `ClassNP`). Without
  `Simulation`: 176; without `Simulation` and `Encoding`: 141.
* **Primitives' public surface** is exactly its 18 existential rows.
* **Witness retirement candidates** (`deps2.py`, privates reached only from one row):
  `computesFunInTime_pairMapSnd` reaches 16 such declarations (447 lines with docstrings:
  `pairMapTM`, `pairMap_computes`, `catalogPayload_computes`, `catalogPayload_length` and 12
  `map*` lemmas); `computesFunInTime_pairDup` reaches 5 (138 lines: `pairDupTM`,
  `pairDup_computes`, `pairDup_double`, `scanCopy_run`, `scanCopy_finish`).
* **Name screen** for the proposed public names (`fullnames.py`, `clash.py`; a namespace-aware
  index of 14,047 declarations of `TCSlib`). No proposed full name exists today except as the
  private witness being renamed or made public in its own home. One short name recurs:
  `Complexity.polyUnaryTM` (P, `ClassNP/TMSAT.lean:145`), in another namespace; TMSAT is in
  `namespace Complexity` with `open Turing` only, so its own private declaration keeps resolving
  first. `TimeHierarchy/Separation.lean` (`open Turing Turing.FinTM TimeHierarchy`) and the
  `CircuitComplexity` files (several `open Turing`; `Advice.lean` has a `namespace Turing.FinTM`
  section) contain no occurrence of any proposed short name, bare or `FinTM.`-qualified. None of
  the proposed short names occurs in the Mathlib sources of the checkout.
* **`TMSAT.lean:145`** declares its own private unary polynomial machine; whether it duplicates
  `catalogPolyUnaryTM` was not measured.

## 5. Line counts of the named files

| File | Lines |
|---|---|
| `Build/Catalog.lean` | 12,752 |
| `Build/Primitives.lean` | 6,309 |
| `Build/Loop.lean` | 4,980 |
| `TuringMachine/Simulation.lean` | 1,014 |
| `Build/Wrappers.lean` | 739 |
| `TuringMachine/Composition.lean` | 685 |
| `TuringMachine/Encoding.lean` | 632 |
| `ClassP/TimeConstructible.lean` | 448 |

## 6. Scripts (`mig1/work/`, all `python3 -I`, read-only on the checkout)

* `decls.py`: declaration scanner (start line, end line, kind, visibility, name), comment-aware.
* `exrows.py`, `exrows_priv.py`, `mclass.py`: statements and conclusions of the public (and
  private) theorems; machine-existential classification.
* `consumers.py`: code and docstring citations of a list of names across all of `TCSlib`.
* `verbatim.py`, `verbatim2.py`, `verbatim3.py`: the verbatim measures of note b.
* `deps.py`, `deps2.py`, `group.py`: dependency closures inside a file; the grouping of §2.3.
* `imports.py`: the import graph and the replay closure.
* `fullnames.py`, `clash.py`: the namespace-aware declaration index and the name screen.
* `mktable.py`, `mkappendix.py`, `rewrap.py`: the tables of §1 and §2.3, and line wrapping.
