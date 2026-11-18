# Pass–shelat cleanup Stage 2, job S2-A (J0 + J1 + J2): in-house work plan r1

**Status: draft for the maintainer and for Seyoon's rulings Q-A1 to Q-A11 (§5). Nothing is issued or committed.** Static
work only (git, `python3 -I`, text tools; no Lean, no `lake`). The machine-readable item list is
[`s2a-items.tsv`](s2a-items.tsv): **435 rows**, one per item, each with its step, tip location, kind, freeze status,
exact intended change and dependencies. Every line number below and in the TSV is at the tip in §0.

## 0. Pins, inputs and method

| Pin | Value |
|---|---|
| Records tip (`origin/cryptography/pass-shelat-ch2-4` after `git fetch`, = local HEAD) | `38123ccbebef878cd25dd2d2761de1b40ba7e421` (snapshot #10 adopted; records-only after `2bff71775d5039e2e23f48b316d6d69b962e03dc`, the #366/#368 records commit) |
| Lean at the tip | `TCSlib` tree `849ee9454cff17b1fb15a22183526d7e071a9669`, identical at `2bff7177` and `38123ccb` (whole tree `13f58be4b59a62eb7eed826a15711b7793f91735`) |
| Plan pin (`plan-r1.md`, `scope.tsv`) | `2be7eb209ae89c9dfe5ba7b63b115ae486ff9ffd`. Between it and the tip 26 TCSlib files changed (GSW 6a, branching programs, `Pairing/Group` #365, `EnsembleSecurity` #368); **none of the 59 S2-A owner files and not `Games/Relational.lean`** (`git diff --quiet` per file). Every `scope.tsv` line was re-verified at the tip by declaration name: 0 mismatches, 0 not found |
| DW-10 inventory base (failing-read and seal-error lines) | `f472accd5e000a53d0fbe02b5414435429ce4a70`; mapped to the tip through `git diff -U0` hunks. 11 S2-A files changed since that base (`IterateFind`, `IterateFindHost`, `PPT`, `ModuleHost`, `IdentityBased/Defs`, `BitLists`, `Games/Probability`, `Games/Tapes`, `Pairing/Assumptions`, `Entropy`, `Games/Relational`) |
| Inputs | `cleanup-stage2/plan-r1.md` (`7d5496ff…8d34cc62`), `scope.tsv` (`59509ea8…b5e5bf91`), `cleanup-stages.md` (`1be85556…a7ae5e7b`), `duplication-ledger.md` (`d500c17e…9b250cf1`), `deferred-work.md` (`6a7c9d30…0ef57ac4`), `cleanup-dw10/final-r1/stage2-seal-items.tsv` (`c0ec4010…e30459b0`) and `stage2-readers.tsv` (`d9ea4be6…9878f3a8`), `cleanup-stage1/final-r1/stage2-addendum.tsv` (`b2656ad5…8a43fa73`), `ingests/ps10-cite-check-final-r1/REPORT.md` (`4390cc6a…0db3f1c8`) |
| Exchange objects read (git objects only) | Stage 1 `repoint.tsv` at `5451d3cd6fa9b8c313c9f18f5a4da3542c85f02a:inbox/fills/cleanup-stage1/evidence/stage2/repoint.tsv` (`8fba3337…b7f9`); DW-10 `inventory.tsv` and `evidence/seal-errors.jsonl` at `57cd9272d5739fae252cf486297c696f7b90d2bd:inbox/audits/dw10-seal-inventory/` (`7e2b2e6a…37b8f`; `ee892226…046a789b`); `stmtcheck.txt` from the DW-10 review evidence ZIP (`16ed839f…174aa91c`) |
| Gate 49 | `briefs/pairings/gates/49-dw11-small-items/findings-r1.md`, `resolutions-r1.md` (G49-01, G49-02) |

**Method.** `scope.tsv` rows with job J0/J1/J2 (425) were joined, by their derivation order, to the DW-10 derivative
(S2-SL ↔ `stage2-seal-items.tsv`, S2-RD ↔ `stage2-readers.tsv`) and to the 194 SEAL-B-ONLY inventory rows (S2-BO), whose
seal-B error lines, messages and providers come from `seal-errors.jsonl`. Re-points, promotions and readers were read in
the source at the tip; exact statements were written from the definitions. The import graph (1,479 modules) was parsed
from the tip's git objects; "downstream" is the reverse-import closure. Scratch tools: `graph.py`, `join.py`,
`build_s2a.py`, `emit_tsv.py`, `texts.py` (session scratchpad; not records).

**Corrections to `scope.tsv` found here.**
- S2-DL-02 (DL-55, pairing T1): the inline verdict identity is in the private `distinguisherL_tupleStr`
  (`Pairing/Assumptions.lean:189–199`, the closing `simp only [List.cons.injEq, and_true, decide_eq_true_eq]`), not in
  `bdhAssumption_of_dbdhAssumption` (l.426, a name match).
- S2-PA-01's site is `IterateFind.lean:314` at the tip (`[PS10, §8.2, Theorem 180.1, step 4]`), confirmed by text.
- The DL-56 reader "if needed" **is** needed (§1.1, S2A-N04): the recorded obstruction is the absence of `_eq` readers
  for `InteractiveHandler.rU/rZ/rW/rS`.
- 15 SEAL-B-ONLY rows classed "proof-level" are **definitions** whose fix changes the body (§1.4, Q-A2).
- 3 STAGE2 rows fail **in the header** under seal B and are not in F01's 51 (§1.3, Q-A3).
- DL-35 #2 breaks an S2-D file if S2-A lands it (§3, Q-A1).

## 1. The S2-A items at the tip

### 1.0 Counts

| kind | J0 | J1 | J2 | total |
|---|---:|---:|---:|---:|
| seal fix (proof-only; DW-10 derivative) | – | 128 | 136 | 264 |
| B-only fix, proof-level | 1 | 2 | 62 | 65 |
| B-only fix, **definition body** (Q-A2) | – | – | 15 | 15 |
| B-only fix, **statement-level** (Q8 freeze exceptions) | – | – | 11 | 11 |
| B header fix, statement-level, **not in F01's 51** (Q-A3) | – | – | 3 | 3 |
| add reader (rows; 30 declarations) | 13 | – | 9 | 22 |
| promote (DL-43, DL-55 move, DL-57, DL-59) | 4 | – | – | 4 |
| re-point | 1 | 3 | 15 | 19 |
| alias change (DL-35 #1, #2, #3, #6) | – | – | 4 | 4 |
| delete (`host_*`; DL-38 `ofFn_chunk`, `fac_ofFn_halves`) | – | 1 | 2 | 3 |
| PS10 Tier A citation fix / Tier B related note | – | 19 | 1 / 1 | 21 |
| doc fix (G49-01, G49-02), doc nit (CS1-C1-F10), records correction (G49-01) | 4 | – | – | 4 |
| **total** | **23** | **153** | **259** | **435** |

425 rows are `scope.tsv`'s (J0 19, J1 153, J2 253); 10 are new here (S2A-N01 to N10). 18 seal fixes are `needs-check`
(F06: `UnaryMul` 1, `Primitives` 1, `EnsemblesLemmas` 3, `HardCore/Functions` 4, `OneWayYao` 8, `Primality` 1); each is
probed first in its step. Estimated changed lines: **~1,846** (the ruling's ~1,770 plus the new items; ±40 %).

### 1.1 J0: promotions and readers (exact statements)

All are additive except DL-55 (a verbatim move, one REMOVED/ADDED pair, same full name) and DL-59 (a universe-only
change of #355 API, ruled Q8). Full text per row in the TSV.

| id | home (tip) | declaration(s) to add or change |
|---|---|---|
| S2-RD-02 | `Complexity/TuringMachine/Encoding.lean` after `CodeTM.toFinTM_k` (l.125) | Q11 provider reader, pure insertion, no `@[simp]`. Recommended (Q-A4a): `theorem CodeTM.toFinTM_computesInTime_iff (M : CodeTM) (x w : List Bool) (t : ℕ) : M.toFinTM.ComputesInTime x w t ↔ (M.tm.runFrom (M.tm.initCfg x) t).state = none ∧ (M.tm.runFrom (M.tm.initCfg x) t).output = w := FinTM.computesInTime_iff M.toFinTM x w t`. The ruled name `toFinTM_tm` names a field equation `M.toFinTM.tm = M.tm`, which is dependent-typed (`MultiTapeTM M.toFinTM.k Bool M.toFinTM.State`) and unusable by `rw`; the literal alternative is `toFinTM_State : M.toFinTM.State = Fin (M.numStates + 1) := rfl` plus `toFinTM_tm : HEq M.toFinTM.tm M.tm := HEq.rfl` (Q-A4c). Consumer `Asymptotic/Universal.lean:139, 151` |
| S2-RD-03 | same file, after `pairDecode_nil` (l.153) | `pairDecode_false_false (r) : pairDecode (false :: false :: r) = (pairDecode r).map fun p => (false :: p.1, p.2) := rfl`; `pairDecode_true_true (r)` (same with `true`); `pairDecode_false_true (r) : pairDecode (false :: true :: r) = some ([], r) := rfl`; `pairDecode_true_false (r) : pairDecode (true :: false :: r) = none := rfl`; `pairDecode_singleton (b : Bool) : pairDecode [b] = none := by cases b <;> rfl`. Not `@[simp]`. Consumers `PairSplit`, `UnaryMul` |
| S2-RD-01 | `Complexity/Randomized/Repetition.lean` after `polyTimeComputable_iterateFind` (l.190) | `theorem polyTimeComputable_iterateFind_elim` with the hypotheses of `polyTimeComputable_iterateFind` (`hg`, `hacc`, `hout`, `R P`, `horbit`) and conclusion `PolyTimeComputable fun x => ((List.range (R.eval x.length + 1)).find? (fun i => acc (g^[i] x))).elim [] (fun i => out (g^[i] x))` (`convert … using 2; cases … <;> rfl`). Consumers `Candidates/Concrete` (S2-A), `GGM/Reduction` (S2-B), `OneWayYao.yaoRaw_eq` (S2-A) |
| S2-BO-033 | `Repetition.lean:406` | `polyTimeComputable_majority`: `le_rfl` → `(PolyExpr.eval_var _).ge` at l.409 (proof-only) |
| S2-DL-10 | `Games/Tapes.lean:139–162` | `{C : Type}` → `{C : Type*}` in `Games.extTape`, `extTape_of_lt`, `extTape_of_not_lt`, `extTape_update` (DL-59; Q8) |
| S2-DL-28 | `Games/Tapes.lean` module docstring | Main-results bullet for `Games.freshImpl_apply`, `Games.tapeImpl_apply` (CS1-C1-F10) |
| S2-DL-16 | `Games/Probability.lean`, `namespace ProbComp` before `section Sampling` (l.296) | `theorem mul_prob_le_expect {α : Type} (c : ProbComp α) (P : α → Prop) (q : α → ℝ) (b : ℝ) (hq : ∀ a, 0 ≤ q a) (hP : ∀ a, P a → b ≤ q a) : b * prob c P ≤ expect c q` (header pinned in the Stage 1 brief, handover 2; proof as `Lamport/Averaging.lean:129`) |
| S2-DL-01, S2-DL-02, S2-RP-042 | `TrapdoorPredictor.lean:143–145` → `Foundations/BitLists.lean` | verbatim move of `theorem decide_singleton_eq_true (b : Bool) : decide ([b] = [true]) = b` (same full name), in one commit with the T1 re-point (`Pairing/Assumptions.lean:199` → `rw [decide_singleton_eq_true]`) and BitLists' own DL-47 re-point (`headD_ofFn_one` via `headD_drop_ofFn`) |
| S2-DL-07 | `IdentityBased/Defs.lean`, `namespace IBEScheme` after `sidSpec_eq` (l.236) | `sidSpec_dom_zero/one (κ) : (S.sidSpec κ).dom 0/1 = (Fin (S.idLen.eval κ) → Bool)`; `sidSpec_dom_two (κ) : … = (Fin (S.msgLen.eval κ + S.msgLen.eval κ) → Bool)`; `sidSpec_rng_zero (κ) : (S.sidSpec κ).rng 0 = (Fin (S.ppLen.eval κ) → Bool)`; `sidSpec_rng_one (κ) : … rng 1 = (Fin (S.skLen.eval κ + 1) → Bool)`; `sidSpec_rng_two (κ) : … rng 2 = (Fin (S.ctLen.eval κ) → Bool)` (each `rw [sidSpec_eq, bitSpec_dom/rng, inLens_*/outLens_*]`); `zeroBits_eq_cast {n m} (hnm : n = m) (e : (Fin m → Bool) = (Fin n → Bool)) : zeroBits n = cast e (zeroBits m)` (home Q-A6) |
| S2-RD-04/05/06 | `Asymptotic/Ensembles.lean`, `namespace Ensemble` | `distAdv_uniform {σ ρ} [Fintype σ] [Fintype ρ] (ℓ) (n) (X : σ → (Fin (ℓ.eval n) → Bool)) (D) : distAdv X ((uniform ℓ).X n) D = distAdv X (id : (Fin (ℓ.eval n) → Bool) → _) D := rfl`; `indist_iff (X Y : Ensemble ℓ) : X.Indist Y ↔ ∀ D : NUPPT, Negligible fun n => distAdv (X.X n) (Y.X n) (D.distinguisher n (ℓ.eval n)) := Iff.rfl`; `samplable_iff (X) : X.Samplable ↔ ∃ (s : PolyExpr) (S : List Bool → List Bool), PolyTimeComputable S ∧ ∀ n, StatClose (fun r : Fin (s.eval n) → Bool => padFin (ℓ.eval n) (S (NUPPT.advInput n (List.ofFn r)))) (X.X n) 0 := Iff.rfl`. Consumer `PRG/Defs` (S2-B) |
| S2-RD-07 | `Asymptotic/EnsemblesLemmas.lean` after `swapAux` (l.503) | `swapAux_apply (ζ S ρ : Type*) (a : ζ) (b : S × ρ) : swapAux ζ S ρ (a, b) = (b.1, (a, b.2)) := rfl`. Consumer `CommitmentLemmas` (S2-D) |
| S2-RD-13/14 | `Asymptotic/Permutations.lean` after l.104 / l.112 | `fisherYates_def (n) (c) : fisherYates n c = (List.finRange n).foldr (fun i σ => Equiv.swap i ⟨(i + c i % (n - i)) % n, _⟩ * σ) 1 := rfl`; `permFromCoins_def (n k T) (b) : permFromCoins n k T b = if h : ∀ i, (rejectionSample (n - i) k T (b i)).isSome then some (fisherYates n fun i => ((rejectionSample (n - i) k T (b i)).get (h i)).val) else none := rfl`. Consumer `EncodingPermutations` (S2-D) |
| S2-RD-26/27/28 | `Pseudorandom/GeneratorFromPermutation.lean` after l.68/73/78 | `owpGen_apply (f) (B) (w) : owpGen f B w = (f w.1, w.2, B w) := rfl`; `owpPair_apply (f) (w) : owpPair f w = (f w.1, w.2) := rfl`; `owpGenNot_apply (f) (B) (w) : owpGenNot f B w = (f w.1, w.2, !B w) := rfl`. Consumers `Trapdoor`, `FromPermutation` (S2-B), `Commitment` (S2-D) |
| S2A-N04 | `Games/Efficiency.lean`, `namespace InteractiveHandler` after l.471 | `rU_eq (w) : rU w = pairFstD (pairFstD w) := rfl`; `rZ_eq (w) : rZ w = pairFstD (pairSndD (pairFstD w)) := rfl`; `rW_eq (w) : rW w = pairSndD (pairSndD (pairFstD w)) := rfl`; `rS_eq (w) : rS w = pairFstD (pairSndD w) := rfl` (DL-56; Q-A5). S2-B re-points `BB1Machine.poly_rU…` |
| S2A-N01, N02 (+N03) | `Games/Relational.lean:16–22`, `:122–129` | G49-01 module-docstring reword (equality of compatible test expectations, not a relation-supported coupling) and G49-02 `[BGZ09, §4.1, rule R-Rand]` with the adaptation note (exact text in the TSV); N03 is the dated correction to `briefs/pairings/fills/bb1-sim/design-r1.md` §2.2 (records) |

### 1.2 J1: Complexity hosts and derandomization

- **DW-9/DW-5 re-points** (S2-RP-001..003, `IterateFind.lean:373/378/390`): the local `hdisp`, `hbranch`, `hhalt` of
  `computesFunInTime_find` become `host_dispatch_view M K hk x w`, `host_branch_view M K hk x b w hw`,
  `host_halt_view M K hk x w o` (identical statements; ~25 lines removed).
- **`host_*` deletion** (S2-RP-004, `IterateFindHost.lean:354/366/382`): delete `host_dispatch`, `host_branch`,
  `host_halt` (no caller since DW-5; resolves the 3 STATEMENT rows, DW10-Q9); reword the docstrings that cite them
  (module docstring l.32–34 and l.48; the `_view` docstrings l.392/407/430).
- **128 seal fixes**: `IterateFindHost` 32, `ModuleHost` 20, `PairSplit` 55 (12 need S2-RD-03), `UnaryMul` 19 (6 need
  S2-RD-03; S2-SL-089 needs private `unaryMulTM` field equations, needs-check), `Primitives` 2. The derivative's fix
  text and the failing line at the tip are in the TSV.
- **B-only**: `PPT.runAtL_ofPolyTimeUniform` (l.440, `eval_const`), `Primitives.polyTimeComputable_unaryPoly`
  (l.158, `simpa only [PolyExpr.eval_const]`).
- **PS10 Tier A** (19): A1 at `IterateFind.lean:314`, `SeedMajority.lean:26, 74, 173, 235`,
  `SeedMajority/Enumeration.lean:42`, `State.lean:70, 99, 142, 155, 183, 220`, `Words.lean:45, 88, 116, 131, 163`
  ("step 4" → "final paragraph of the proof"); A2 at `SeedMajority.lean:83` and `RootSchedule.lean:16` (REPORT's
  corrections, exact text in the TSV). `IterateFind` is re-sealed by the gate (F-01, DW10-F13).

### 1.3 J2: the statement-level fixes, one by one (freeze exceptions)

Convention (Q-A9a): the binder stays at the family's own `PolyExpr` type, so the left-hand side still matches every use;
concrete-length views go through `Fin.cast` of published `*_eval` readers (or the published `*_domEquiv`/`*_codEquiv`,
`glPad_inEquiv`/`glPad_outEquiv`). Each restatement is meaning-preserving: `Fin.cast h` is the identity on values and,
for `h` provable by `rfl`, definitionally the identity, so every instance of the old statement is an instance of the new.

| # | id | owner:line | current header (abridged) | proposed header | consumers |
|---|---|---|---|---|---|
| 1 | S2-BO-001 | `Asymptotic/Ensembles.lean:232` | `theorem copies_X (t : PolyExpr) (X : Ensemble ℓ) (n : ℕ) (s : Fin (t.eval n) → X.σ n) (i : Fin (t.eval n * ℓ.eval n)) : (X.copies t).X n s i = X.X n (s (finProdFinEquiv.symm i).1) (finProdFinEquiv.symm i).2` | `theorem copies_X (t : PolyExpr) (X : Ensemble ℓ) (n : ℕ) (s : Fin (t.eval n) → X.σ n) (i : Fin ((PolyExpr.mul t ℓ).eval n)) : (X.copies t).X n s i = X.X n (s (finProdFinEquiv.symm (Fin.cast (PolyExpr.eval_mul t ℓ n) i)).1) (finProdFinEquiv.symm (Fin.cast (PolyExpr.eval_mul t ℓ n) i)).2` | no consumers |
| 2 | S2-BO-036 | `Asymptotic/Collections.lean:927 (private)` | `private theorem collInverter_success … (hz' : A'.runAt n (List.ofFn ((G.owfFamily L).f n ((G.owfCoinsEquiv n).symm ((splitCoins …).symm (r₁, r₂))))) ρ = List.ofFn z') (hg : (G.owfFamily L).f n ((G.owfCoinsEquiv n).symm z') = (G.owfFamily L).f n ((G.owfCoinsEquiv n).symm ((splitCoins …).symm (r₁, r₂)))) : …` | `same, with each of the three family arguments (G.owfCoinsEquiv n).symm Z written (G.owfCoinsEquiv n).symm Z ∘ Fin.cast (G.owfFamily_inLen_eval L n) (new reader S2A-N06); conclusion unchanged` | private; in-file only |
| 3 | S2-BO-037 | `Asymptotic/Collections.lean:987 (private)` | `private theorem fiber_le … uprob (fun v => ∃ w : Fin ((G.owfFamily L).inLen.eval n) → Bool, A'.runAt n (List.ofFn ((G.owfFamily L).f n ((G.owfCoinsEquiv n).symm ((splitCoins …).symm (r₁, v.1))))) v.2 = List.ofFn w ∧ (G.owfFamily L).f n w = (G.owfFamily L).f n ((G.owfCoinsEquiv n).symm …)) ≤ …` | `same, with the two (G.owfCoinsEquiv n).symm Z family arguments written … ∘ Fin.cast (G.owfFamily_inLen_eval L n); binder w unchanged` | private; in-file only |
| 4 | S2-BO-069 | `HardCorePermutation/GoldreichLevin.lean:606 (private)` | `private theorem ofFn_oddCoins (A : NUPPT) (m : ℕ) {post} (hpost) (e : Bool) (c : A.Coins (m + m + 1)) : List.ofFn (oddCoins A m hpost (e, c)) = List.ofFn (fun _ : Fin 1 => e) ++ List.ofFn (NUPPT.reparamCoins A oddParam m c)` | `… = List.ofFn (fun _ : Fin 1 => e) ++ List.ofFn (NUPPT.reparamCoins A oddParam m (c ∘ Fin.cast (congrArg A.coinLen (oddParam_eval m))))  (new private reader S2A-N07 oddParam_eval (m) : oddParam.eval m = m + m + 1)` | private; in-file only (with S2-BO-064/065/068) |
| 5 | S2-BO-072 | `Asymptotic/OneWay.lean:362` | `theorem ofFn_ofString_f {f p} (hf : LengthRegular f p) (n : ℕ) (x : Fin n → Bool) : List.ofFn ((ofString f p).f n x) = f (List.ofFn x)` | `theorem ofFn_ofString_f {f p} (hf : LengthRegular f p) (n : ℕ) (x : Fin n → Bool) : List.ofFn ((ofString f p).f n (x ∘ Fin.cast (ofString_inLen_eval f p n))) = f (List.ofFn x)` | in-file: ofFn_ofString_apply (l.369, S2-BO-071) becomes the primary proof; ofString_id_f re-proved |
| 6 | S2-BO-073 | `Asymptotic/OneWay.lean:375` | `theorem ofString_id_f (n : ℕ) (x : Fin n → Bool) : (ofString id .var).f n x = x` | `theorem ofString_id_f (n : ℕ) (x : Fin n → Bool) : (ofString id .var).f n (x ∘ Fin.cast (ofString_inLen_eval id .var n)) = x ∘ Fin.cast ((ofString_outLen_eval id .var n).trans (PolyExpr.eval_var n))` | in-file: l.873, 924 (`rw [hA, FunFamily.ofString_id_f]`) adapt |
| 7 | S2-BO-076 | `Asymptotic/OneWay.lean:407` | `theorem prod_f (𝓕 : FunFamily) (q : PolyExpr) (n : ℕ) (x : Fin (q.eval n * 𝓕.inLen.eval n) → Bool) : (𝓕.prod q).f n x = (blocks (q.eval n) (𝓕.outLen.eval n)).symm (OneWay.prodFun (𝓕.f n) (q.eval n) (blocks (q.eval n) (𝓕.inLen.eval n) x))` | `theorem prod_f (𝓕 : FunFamily) (q : PolyExpr) (n : ℕ) (x : Fin ((𝓕.prod q).inLen.eval n) → Bool) : (𝓕.prod q).f n x = (blocks (q.eval n) (𝓕.outLen.eval n)).symm (OneWay.prodFun (𝓕.f n) (q.eval n) (blocks (q.eval n) (𝓕.inLen.eval n) (x ∘ Fin.cast (𝓕.prod_inLen_eval q n).symm))) ∘ Fin.cast (𝓕.prod_outLen_eval q n)  (new readers S2A-N05)` | in-file: l.428, 454 |
| 8 | S2-BO-084 | `Asymptotic/OneWay.lean:957` | `@[simp] theorem PermFamily.toFunFamily_f (P : PermFamily) (n : ℕ) (x : Fin n → Bool) : P.toFunFamily.f n x = P.f n x` | `@[simp] theorem PermFamily.toFunFamily_f (P : PermFamily) (n : ℕ) (x : Fin (P.toFunFamily.inLen.eval n) → Bool) : P.toFunFamily.f n x = (P.toFunFamily_codEquiv n).symm (P.f n (P.toFunFamily_domEquiv n x))  (simp attribute per Q-A8)` | @[simp]: implicit uses; consumers found only in S2-A files (HardCore/Functions, GoldreichLevin); Commitment.lean (S2-D) uses toFunFamily.Easy only |
| 9 | S2-BO-112 | `Candidates/Factoring.lean:702 (private)` | `private theorem fac_prodInverter_eq_yaoB (A : NUPPT) (n : ℕ) (Y : Fin (fmultBlocks.eval n) → (Fin (2 * n) → Bool)) (r : A.Coins n) (i) (hp) : prodInverter A n Y r i = OneWay.yaoB fmult.inLen fmult.outLen fmultBlocks A n Y r i` | `… : prodInverter A n Y r i = OneWay.yaoB fmult.inLen fmult.outLen fmultBlocks A n (fun j => Y j ∘ Fin.cast (fmult_outLen n)) r i ∘ Fin.cast (fmult_inLen n).symm` | private; in-file only |
| 10 | S2-BO-117 | `Candidates/Factoring.lean:155` | `theorem fmult_f (n : ℕ) (x : Fin (2 * n) → Bool) : fmult.f n x = natToBits (2 * n) (fmultNat (bitsToNat (FunFamily.blocks 2 n x 0)) (bitsToNat (FunFamily.blocks 2 n x 1)))` | `theorem fmult_f (n : ℕ) (x : Fin (fmult.inLen.eval n) → Bool) : fmult.f n x = natToBits (2 * n) (fmultNat (bitsToNat (FunFamily.blocks 2 n (x ∘ Fin.cast (fmult_inLen n).symm) 0)) (bitsToNat (FunFamily.blocks 2 n (x ∘ Fin.cast (fmult_inLen n).symm) 1))) ∘ Fin.cast (fmult_outLen n)` | in-file: l.173, 252, 538, 963 (+ Fin.cast_trans/Fin.cast_eq_self cleanup) |
| 11 | S2-BO-119 | `Candidates/Factoring.lean:170` | `theorem fmult_inv_factor {n p q : ℕ} (hp hq hpn hqn) (x' : Fin (2 * n) → Bool) (h : fmult.f n x' = natToBits (2 * n) (p * q)) : bitsToNat (FunFamily.blocks 2 n x' 0) = p ∨ … = q` | `same with (h : fmult.f n (x' ∘ Fin.cast (fmult_inLen n)) = natToBits (2 * n) (p * q) ∘ Fin.cast (fmult_outLen n)); conclusion unchanged` | in-file: l.543, 967 |
| 12 | S2A-N08 (Q-A3) | `Asymptotic/HardCore/Functions.lean:272` | `theorem glPad_f (n : ℕ) (x r : Fin (𝓕.inLen.eval n) → Bool) : 𝓕.glPad.f n (Fin.append x r) = Fin.append (𝓕.f n x) r` | `theorem glPad_f (n : ℕ) (x r : Fin (𝓕.inLen.eval n) → Bool) : 𝓕.glPad.f n ((𝓕.glPad_inEquiv n).symm (Fin.append x r)) = (𝓕.glPad_outEquiv n).symm (Fin.append (𝓕.f n x) r)  (glPad_f_equiv l.288 then by rw [glPad_f, Equiv.apply_symm_apply])` | HardCore/Functions (glPad_f_equiv, S2-SL-164..167), HardCoreCollection (1 use) |
| 13 | S2A-N09 (Q-A3) | `Asymptotic/HardCore/Functions.lean:280` | `theorem glBit_append (n : ℕ) (x r : Fin (𝓕.inLen.eval n) → Bool) : 𝓕.glBit n (Fin.append x r) = HardcoreBit.ip x r` | `theorem glBit_append (n : ℕ) (x r : Fin (𝓕.inLen.eval n) → Bool) : 𝓕.glBit n ((𝓕.glPad_inEquiv n).symm (Fin.append x r)) = HardcoreBit.ip x r  (= the existing glBit_equiv, l.294; glBit_equiv kept as glBit_append n x r, or glBit_append deprecated to it per Q-A3)` | HardCore/Functions (3), GoldreichLevin (3) |
| 14 | S2A-N10 (Q-A3) | `Asymptotic/Universal.lean:702 (private)` | `private theorem invProbAt_reduction_ge … : 1 - 1 / (n : ℝ) ^ 2 ≤ (⟨.var, L, g⟩ : FunFamily).invProbAt B (n - Nat.log 2 n)` | `… : 1 - 1 / (n : ℝ) ^ 2 ≤ (⟨.var, L, fun m x => g m (x ∘ Fin.cast (PolyExpr.eval_var m).symm)⟩ : FunFamily).invProbAt B (n - Nat.log 2 n)  (one private helper varFamily L g shared with fUniversal_hard l.898, S2-BO-092)` | private; in-file only |

Rows 1–11 are F01's J2 share of the 51 (Q8, granted). Rows 12–14 are not among the 51: they are STAGE2 rows
whose A-failure is in the body (fixed by S2-RD-15 or the local proof) but whose **seal-B failure is in the header**
(`stmtcheck.txt`: `glPad_f`, `glBit_append`, `invProbAt_reduction_ge`; 57 header-failing declarations = 3 `host_*` + 51
+ these 3). The Stage 2 target (coe-B = 0 in touched owners) needs them restated: Q-A3. Support readers added for the
restatements: S2A-N05 `FunFamily.prod_inLen_eval`, `prod_outLen_eval` (`OneWay.lean`), S2A-N06
`Collection.owfFamily_inLen_eval` (`Collections.lean`), S2A-N07 private `oddParam_eval` (`GoldreichLevin.lean`).
All consumers of rows 1–14 are in S2-A files (checked by `git grep`; `PermFamily.toFunFamily_f` is `@[simp]`, and the
only other file naming `toFunFamily` is `ZeroKnowledge/Commitment.lean:874`, which uses `toFunFamily.Easy` only).

### 1.4 J2: SEAL-B-ONLY rows that are definitions (body changes; Q-A2)

The inventory class "proof-level" means "no header error"; for a definition, the failing term is its body. The fix
is a cast through `PolyExpr.eval_*` (or a published `*_eval` reader), definitionally equal to the old body (casts
along `rfl`-provable equations reduce, and `Fin`/`Equiv` structure eta closes the rest). The gate's decls2 will show
them CHANGED, so they need listing like Q7's bodies. Consumers that unfold these bodies are all in S2-A files
(`git grep` over unfold/simp/rw lists; the `glPad`/`glBit` uses in `HardcoreBit/InnerProduct.lean` are the other
namespace's definitions).

| id | owner:line | definition | body change (definitional) |
|---|---|---|---|
| S2-BO-039 | `Asymptotic/Collections.lean:718` | `owfFamily` | owfFamily body: `G.owfCoinsEquiv n r` -> `G.owfCoinsEquiv n (r ∘ Fin.cast (PolyExpr.eval_add G.gen.coins G.sample.coins n).symm)` (both occurrences) |
| S2-BO-041 | `Asymptotic/Ensembles.lean:223` | `copies` | Ensemble.copies body: `(FunFamily.blocks (t.eval n) (ℓ.eval n)).symm (…) ∘ Fin.cast (PolyExpr.eval_mul t ℓ n)` (with S2-BK-06) |
| S2-BO-042 | `Asymptotic/HardCore/Functions.lean:225` | `glBit` | glBit body: argument `z` of `(Fin.appendEquiv …).symm` -> `z ∘ Fin.cast (𝓕.glPad_inLen_eval n).symm` (or `𝓕.glPad_inEquiv n z` once S2-BO-045 is fixed) |
| S2-BO-043 | `Asymptotic/HardCore/Functions.lean:231` | `glInverter` | glInverter body: `y` -> `y ∘ Fin.cast (𝓕.glPad_outLen_eval n).symm` (or `𝓕.glPad_outEquiv n y`) |
| S2-BO-044 | `Asymptotic/HardCore/Functions.lean:217` | `glPad` | glPad body: `z` -> `z ∘ Fin.cast (PolyExpr.eval_add 𝓕.inLen 𝓕.inLen n).symm`; output `… ∘ Fin.cast (PolyExpr.eval_add 𝓕.outLen 𝓕.inLen n)` |
| S2-BO-045 | `Asymptotic/HardCore/Functions.lean:245` | `glPad_inEquiv` | glPad_inEquiv := `Equiv.arrowCongr (finCongr (𝓕.glPad_inLen_eval n)) (Equiv.refl Bool)` (was `Equiv.refl _`) |
| S2-BO-049 | `Asymptotic/HardCore/Functions.lean:251` | `glPad_outEquiv` | glPad_outEquiv := `Equiv.arrowCongr (finCongr (𝓕.glPad_outLen_eval n)) (Equiv.refl Bool)` (was `Equiv.refl _`) |
| S2-BO-055 | `Asymptotic/HardCoreCollection.lean:92` | `glPad` | HardCoreCollection glPad body (l.121): coin argument `(NUPPT.coinsEquiv_ofPolyTimeUniform … (F.sample.coins.add m) n) s` -> `… ∘ Fin.cast (PolyExpr.eval_add F.sample.coins m n).symm` |
| S2-BO-068 | `Asymptotic/HardCorePermutation/GoldreichLevin.lean:596` | `oddCoins` | oddCoins body: transport `A.Coins (m + m + 1)` to `A.Coins (oddParam.eval m)` by `Fin.cast (congrArg A.coinLen (oddParam_eval m))` (S2A-N07) and `(PolyExpr.const 1).eval m` by `PolyExpr.eval_const` |
| S2-BO-075 | `Asymptotic/OneWay.lean:243` | `prod` | FunFamily.prod body: input `x ∘ Fin.cast (PolyExpr.eval_mul q 𝓕.inLen n).symm`; output `… ∘ Fin.cast (PolyExpr.eval_mul q 𝓕.outLen n)` |
| S2-BO-078 | `Asymptotic/OneWay.lean:937` | `toFunFamily` | PermFamily.toFunFamily body: `f n x := P.f n (x ∘ Fin.cast (PolyExpr.eval_var n).symm) ∘ Fin.cast (PolyExpr.eval_var n)` (was `P.f n`) |
| S2-BO-079 | `Asymptotic/OneWay.lean:973` | `toFunFamily_codEquiv` | toFunFamily_codEquiv := `Equiv.arrowCongr (finCongr (P.toFunFamily_outLen_eval n)) (Equiv.refl Bool)` (was `Equiv.refl _`) |
| S2-BO-081 | `Asymptotic/OneWay.lean:969` | `toFunFamily_domEquiv` | toFunFamily_domEquiv := `Equiv.arrowCongr (finCongr (P.toFunFamily_inLen_eval n)) (Equiv.refl Bool)` (was `Equiv.refl _`) |
| S2-BO-115 | `Candidates/Factoring.lean:142` | `fmult` | fmult body: input `x ∘ Fin.cast h.symm`, output `… ∘ Fin.cast h` with `h : ((PolyExpr.const 2).mul PolyExpr.var).eval n = 2 * n := by rw [PolyExpr.eval_mul, PolyExpr.eval_const, PolyExpr.eval_var]` (or fmult_inLen/fmult_outLen after S2-BO-118/120) |
| S2-BO-121 | `Candidates/Factoring.lean:675` | `plantFactor` | plantFactor body: `fmult.f n` -> `fun x => fmult.f n (x ∘ Fin.cast (fmult_inLen n)) ∘ Fin.cast (fmult_outLen n).symm` |

### 1.5 J2: re-points, DL-35, deletions, PS10

| id | site (tip) | from → to |
|---|---|---|
| S2-BK-01 | `EnsemblesLemmas.lean:815` `exists_copiesRed` (statement, l.821–823) | `blocks` → `FunFamily.blocks` (CS1-Q2 #1); proof uses l.835–850 (S2-BK-17) |
| S2-BK-02 | `EnsemblesLemmas.lean:433` `ofFn_blocks_symm` (statement) | `blocks` → `FunFamily.blocks` (CS1-Q2 #2). **Breaks `ZeroKnowledge/Commitment.lean:852–853` (S2-D); proposed to move to S2-D (Q-A1)** |
| S2-BK-03 | `EnsemblesLemmas.lean:427` `take_drop_ofFn_blocks` (statement) | `blocks q s w ⟨i, hi⟩` → `FunFamily.blocks q s w ⟨i, hi⟩`, proof `FunFamily.ofFn_blocks` (CS1-Q2 #3). External uses (`EncryptThenTag/CPAHandler.lean:534`, `Handler.lean:528`, `CommitmentLemmas.lean:497`) are `exact`/term `have`: still compile |
| S2-BK-06 | `Ensembles.lean:223` `Ensemble.copies` (body) | private `blocks` → `FunFamily.blocks` (CS1-Q2 #6), together with S2-BO-041's cast; S2-BK-15: proof uses l.514, 550–552 |
| S2-RP-030 | `EnsemblesLemmas.lean:433` | proof → `FunFamily.ofFn_blocks_symm_eq_flatMap V F hF` (proof-only; stays in S2-A whatever Q-A1 says) |
| S2-RP-031 | `Hashing/FromDiscreteLog/Probability.lean:40` | body → `Games.Bridge.expect_sample_eq_uexp f`; **adds `import TCSlib.Cryptography.Games.Bridges.Experiments`** (acyclic, +1 module in the closure) |
| S2-RP-032 | `Hashing/FromDiscreteLog/Encoding.lean:45, 55` | bodies → `Authentication.ofFn_splitBits_fst/_snd w` (names kept) |
| S2-RP-038 | `Asymptotic/BlockEncryptor.lean:60` | body → `PrivateKeyScheme.encodeList_eq_flatMap l` (name kept for Lamport's S2-B uses) |
| S2-RP-042 | `Foundations/BitLists.lean:100` | `headD_ofFn_one` via `headD_drop_ofFn` (in step A05 with DL-55) |
| S2-RP-046 | `Asymptotic/HardCoreLoops.lean:260` (`orbit_eq`, chain l.278–280) | → `headD_drop_ofFn` |
| S2-RP-059, S2-RP-060 | `Encoding/BooleanVector.lean:142`, `Hashing/SIS/CollisionOutput.lean:188` | inline getD chains → `getD_ofFn` |
| S2-RP-064, 065, 066 | `CollectionsHelpers.lean:112`; `FromDiscreteLog.lean:97, 134`; `Collections.lean:796, 804` | inline `List.length_ofFn, NUPPT.coinLen_eq` → `NUPPT.length_ofFn_coins` |
| S2-RP-082 | `Candidates/DDH.lean:145` | body → `StatClose.of_uprob_ne X Y` (name kept for `ElGamal.lean:1154`, S2-B) |
| S2-RP-088 | `Encoding/DyadicUniform.lean:83, 148, 216` | optional near-copy re-derivation: recommended no change, CS1-Q10 note (Q-A7) |
| S2-DL-24 | `NumberTheory/Primality.lean:780` private `ofFn_chunk` | delete; uses l.839, 877 → `FunFamily.ofFn_blocks` (keep and re-prove if `chunk` is not definitionally `FunFamily.blocks`) |
| S2-DL-26 | `Candidates/Factoring.lean:198` private `fac_ofFn_halves` | delete; uses l.247, 548, 799 → `FunFamily.ofFn_blocks` / `OneWay.ofFn_block_eq_take_drop` |
| S2-PA-29 | `Hashing/CollisionResistant.lean:52–54` (docstring of l.45) | "in Construction 142.2 the exponents range over `Z_{p−1}`" → "in protocol 142.2 the input `x` is an `n`-bit string (the proof of Theorem 142.3 treats it as an element of `Z*_p`); the repository restricts it to `x < p − 1`" (A8) |
| S2-PR-06 | `Hashing/FromDiscreteLog.lean:709` | "[PS10, probability bound in Theorem 142.3]" → "[PS10, Theorem 142.3; the additive `(1/2)^n` is a repository term from the bounded sampler, see the proof sketch of the main theorem]" (REPORT §3; Q4) |
| S2-RD-08 to RD-12, RD-15 | `HardCoreLoops`, `OneWay`, `OneWayYao`, `InnerProduct` | readers, exact statements in the TSV: `SelXor.input_eq`, `FunFamily.lengthRegular_iff` (`LengthRegular f p ↔ ∀ x, (f x).length = p.eval x.length := Iff.rfl`), `FunFamily.ofString_inLen` (`(ofString f p).inLen = .var := rfl`), `YaoMachine.sampleAll_eq` (function form through `blocksE` and `roundSample`), `YaoMachine.yaoRaw_eq` (in the `Option.elim` form, so `yaoRaw_poly` uses S2-RD-01), `HardcoreBit.glBit_eq` (`glBit (x, r) = ip x r := rfl`) |

The 136 J2 seal fixes and 62 proof-level B-only fixes are listed one by one in the TSV: seal fixes with the
derivative's fix text and the failing line mapped to the tip; B-only fixes with the seal-B error (line, column,
class, expected/actual types) and the `PolyExpr.eval_*` readers it calls for. Recipe for the B-only rows: do not unfold
`PolyExpr.eval`; rewrite with `eval_var/const/add/mul/pow/normal/subst` (`Randomized/PolyExpr.lean:116–131`), or cast
along a published `*_eval` reader; length readers proved by `rfl` (`fmult_inLen`, `eval_fmultBlocks`, `ρP_eval`,
`eval_univOutLen`, `eval_rsa*`, `eval_ddhLen`, `toFunFamily_*Len_eval`, `glPad_*Len_eval`, `eval_yaoBlocks/Rounds`,
`eval_samplePrimeCoins`, `ofString_inLen_eval`) are re-proved by `simp only [<own definition>, PolyExpr.eval_*]`, with
statements unchanged, and are fixed first in their file because the restatements and body casts use them.

## 2. Step sequence

One commit per step, each ≤ ~150 changed lines (largest ~88). Columns: items; estimated changed lines; changed
modules; **downstream** = modules that import a changed module transitively (rebuild set minus the changed ones);
**direct** = direct importers (re-check these at the step when the step changes a statement, a body, a universe or
deletes a declaration); **path** = modules between earlier changed modules of the same batch and this step's files
(re-check first only in a strict replay; additive and proof-only steps can rely on the batch replay). **>300** marks
deep steps; they are batched.

**Batches.** D1 = A01–A18 (J0 + J1; 25 changed modules; one replay of the rebuild set, **776** modules of 1,479). D2 =
A19–A38 (J2 + G49; 38 changed modules; rebuild set **339**). The whole of S2-A touches 61 modules with a rebuild set of
798. Within a batch: check each step's changed files with `scripts/lean_check_tree.sh` in dependency order (and its
direct importers when the step is statement-visible), then replay the batch's rebuild set once (`workflow.md` §6.1),
then the four seal variants on the batch's owners. Recommended (Q-A10a).

| step | job | content | items | lines | changed modules | downstream | direct | path | after |
|---|---|---|---:|---:|---|---:|---:|---:|---|
| A01 | J0 | Q11 provider readers in Encoding.lean (pure insertion) | 2 | ~16 | `Cx/TuringMachine/Encoding` | 755 **>300** | 27 | 0 | - |
| A02 | J0 | iterateFind elim reader + majority B-fix (Repetition) | 2 | ~12 | `Cx/Randomized/Repetition` | 350 **>300** | 21 | 18 | - |
| A03 | J0 | DL-59: Games.extTape at Type* + Tapes docstring nit | 2 | ~10 | `Games/Tapes` | 2 | 1 | 0 | - |
| A04 | J0 | DL-43: ProbComp.mul_prob_le_expect | 1 | ~14 | `Games/Probability` | 189 | 9 | 0 | - |
| A05 | J0 | DL-55 verbatim move to Foundations/BitLists + Pairing re-point + BitLists DL-47 re-point | 3 | ~18 | `Encryption/PublicKey/TrapdoorPredictor`, `Foundations/BitLists`, `Pairing/Assumptions` | 382 **>300** | 30 | 26 | - |
| A06 | J0 | DL-57: IBEScheme.sidSpec_*/zeroBits_eq_cast promotion | 1 | ~40 | `AdvancedEncryption/IdentityBased/Defs` | 16 | 2 | 18 | - |
| A07 | J0 | Cross-job readers in Asymptotic (Ensembles, EnsemblesLemmas, Permutations) | 6 | ~48 | `Asymptotic/Ensembles`, `Asymptotic/EnsemblesLemmas`, `Asymptotic/Permutations` | 275 | 18 | 25 | - |
| A08 | J0 | Cross-job readers in GeneratorFromPermutation | 3 | ~24 | `Pseudorandom/GeneratorFromPermutation` | 237 | 8 | 0 | - |
| A09 | J0 | DL-56 readers in Games/Efficiency (Q-A5) | 1 | ~16 | `Games/Efficiency` | 94 | 12 | 80 | Q-A5 |
| A10 | J1 | ModuleHost seal fixes (DW-9) | 20 | ~80 | `Cx/TuringMachine/Build/ModuleHost` | 407 **>300** | 4 | 0 | - |
| A11 | J1 | IterateFindHost: delete host_* (DW10-Q9) + seal fixes copy_clean/copy_finish | 12 | ~46 | `Cx/Randomized/Build/IterateFindHost` | 354 **>300** | 1 | 1 | - |
| A12 | J1 | IterateFindHost: remaining seal fixes | 21 | ~66 | `Cx/Randomized/Build/IterateFindHost` | 354 **>300** | 1 | 1 | A11 |
| A13 | J1 | PairSplit seal fixes, part 1 (pairDecode readers) | 28 | ~87 | `Cx/Randomized/Build/PairSplit` | 370 **>300** | 2 | 1 | A01 |
| A14 | J1 | PairSplit seal fixes, part 2 | 27 | ~88 | `Cx/Randomized/Build/PairSplit` | 370 **>300** | 2 | 1 | A13 |
| A15 | J1 | UnaryMul seal fixes (incl. needs-check SL-089 private field equations) | 19 | ~60 | `Cx/Randomized/Build/UnaryMul` | 369 **>300** | 1 | 2 | A01 |
| A16 | J1 | Primitives + PPT: seal and B-only fixes | 4 | ~16 | `Cx/Randomized/PPT`, `Cx/Randomized/Primitives` | 417 **>300** | 17 | 7 | A13–A15 |
| A17 | J1 | IterateFind: hdisp/hbranch/hhalt -> host_*_view; PS10 A1 site | 4 | ~14 | `Cx/Randomized/Build/IterateFind` | 353 **>300** | 2 | 10 | A11, A12 |
| A18 | J1 | PS10 Tier A, Theorem 180.1 (SeedMajority family, RootSchedule) | 18 | ~36 | `Cx/Randomized/SeedMajority`, `Cx/Randomized/SeedMajority/Enumeration`, `Cx/Randomized/SeedMajority/State`, `Cx/Randomized/SeedMajority/Words`, `Randomness/Derandomization/RootSchedule` | 8 | 5 | 69 | - |
| A19 | J2 | NumberTheory + InformationTheory (+ SamplingFinDist) | 18 | ~73 | `Asymptotic/SamplingFinDist`, `NumberTheory/Chebyshev`, `NumberTheory/Primality`, `InformationTheory/Entropy`, `InformationTheory/LeftoverHash` | 80 | 10 | 0 | D1 replay |
| A20 | J2 | InnerProduct reader + seal; GoldreichLevinDomain; Hashing re-points + PS10 A8 | 15 | ~66 | `Asymptotic/GoldreichLevinDomain`, `Encoding/BooleanVector`, `HardcoreBit/InnerProduct`, `Hashing/CollisionResistant`, `Hashing/FromDiscreteLog`, `Hashing/FromDiscreteLog/Encoding`, `Hashing/FromDiscreteLog/Probability`, `Hashing/SIS/CollisionOutput` | 203 | 17 | 11 | D1 replay |
| A21 | J2 | CollectionsHelpers + EnsemblesLemmas (DL-35 #1/#3, re-points, seal) | 16 | ~64 | `Asymptotic/CollectionsHelpers`, `Asymptotic/EnsemblesLemmas` | 300 | 26 | 0 | A07 |
| A22 | J2 | OneWayYao (yaoRaw_eq/sampleAll_eq readers, seal, B-only) | 17 | ~76 | `Asymptotic/OneWayYao` | 234 | 1 | 0 | A02 |
| A23 | J2 | OneWay part 1: readers, length readers, definition bodies | 12 | ~60 | `Asymptotic/OneWay` | 233 | 12 | 1 | - |
| A24 | J2 | OneWay part 2: 4 statement-level headers + remaining B-only | 13 | ~68 | `Asymptotic/OneWay` | 233 | 12 | 1 | A23 |
| A25 | J2 | Ensembles: copies body (DL-35 #6 + B cast), copies_X header, alias proof uses | 4 | ~24 | `Asymptotic/Ensembles` | 222 | 3 | 1 | A07, A21 |
| A26 | J2 | Ensembles seal fixes | 20 | ~80 | `Asymptotic/Ensembles` | 222 | 3 | 1 | A25 |
| A27 | J2 | UniversalLemmas + UniversalPadding + BlockEncryptor | 19 | ~76 | `Asymptotic/BlockEncryptor`, `Asymptotic/UniversalLemmas`, `Asymptotic/UniversalPadding` | 90 | 7 | 9 | A23, A24 |
| A28 | J2 | Collections (owfFamily body, 2 private headers) + Concrete | 10 | ~52 | `Asymptotic/Collections`, `Candidates/Concrete` | 214 | 11 | 7 | A02, A23 |
| A29 | J2 | Universal (Q11 consumer; private header Q-A3) | 17 | ~74 | `Asymptotic/Universal` | 2 | 1 | 7 | A01, A23 |
| A30 | J2 | Factoring (fmult body, 3 headers, DL-38 delete) | 13 | ~70 | `Candidates/Factoring` | 8 | 2 | 9 | A23, A24 |
| A31 | J2 | RSA, Rabin, DDH, DyadicUniform (Q-A7) | 8 | ~40 | `Candidates/DDH`, `Candidates/RSA`, `Candidates/Rabin`, `Encoding/DyadicUniform` | 13 | 6 | 16 | A30 |
| A32 | J2 | HardCoreLemmas + HardCoreLoops | 13 | ~56 | `Asymptotic/HardCoreLemmas`, `Asymptotic/HardCoreLoops` | 191 | 5 | 13 | A20 |
| A33 | J2 | HardCoreGL + HardCoreGLColl + HardCoreGLFamily | 13 | ~52 | `Asymptotic/HardCoreGL`, `Asymptotic/HardCoreGLColl`, `Asymptotic/HardCoreGLFamily` | 178 | 2 | 15 | A32 |
| A34 | J2 | HardCoreCollection | 15 | ~60 | `Asymptotic/HardCoreCollection` | 177 | 4 | 17 | A33 |
| A35 | J2 | HardCore/Functions part 1: glPad family bodies, length readers, glPad_f/glBit_append headers (Q-A3) | 13 | ~58 | `Asymptotic/HardCore/Functions` | 172 | 3 | 19 | A20, A34 |
| A36 | J2 | HardCore/Functions part 2: seal fixes + remaining B-only | 14 | ~56 | `Asymptotic/HardCore/Functions` | 172 | 3 | 19 | A35 |
| A37 | J2 | GoldreichLevin (oddCoins body, ofFn_oddCoins header) | 7 | ~32 | `Asymptotic/HardCorePermutation/GoldreichLevin` | 171 | 3 | 20 | A35, A36 |
| A38 | J0 | Games/Relational G49-01/G49-02 docstrings (+ records correction) | 3 | ~18 | `Games/Relational` | 9 | 3 | 0 | A04 (none in S2-A) |

Notes on the order.
- J0 first (A01–A09), then J1 in the hosts' dependency order (`ModuleHost` → `IterateFindHost` → `PairSplit` →
  `UnaryMul` → `Primitives`/`PPT` → `IterateFind` → `SeedMajority`), then J2 by owner group in import order, then the
  G49 docstrings (A38, independent; it can run at any point).
- A01, A02, A05, A10–A17 are the deep steps (350–755 downstream modules each). They all fall in D1, whose rebuild set
  (776) is barely larger than A01's alone (755), so a single D1 replay covers them.
- A21's downstream (300) is at the threshold; it rides in D2.
- Statement-visible steps: A03 (universe), A05 (move), A11 (deletion), A21 (DL-35 #1/#3), A23–A25, A28–A30, A35, A37
  (bodies and headers). Re-check their direct importers in the step.
- S2-BK-02 is not scheduled (Q-A1a: S2-D). If Q-A1b is chosen it joins A21 with the two-line `Commitment.lean` fix.

## 3. Crossings with S2-B, S2-C and S2-D

**Files shared with other jobs (sequential, S2-A first).**
- `Encryption/PublicKey/TrapdoorPredictor.lean`: S2-A deletes l.143–145 (the DL-55 move, A05); S2-B's seal fixes at
  l.111 (S2-SL-270/271) and l.151 (S2-SL-272/273) shift to l.111 and l.147. S2-B pins on the post-S2-A tip.
- `Asymptotic/Ensembles.lean`, `Asymptotic/EnsemblesLemmas.lean`: S2-A adds readers (A07) and does DL-35 #1, #3, #6
  (A21, A25); S2-D's closer removes the aliases (S2-BK-21/22) after S2-B and S2-D have moved their sites.

**S2-A items that would touch S2-B/C/D files: one.** DL-35 #2 (S2-BK-02) breaks `ZeroKnowledge/Commitment.lean:852–853`
(S2-D), which rewrites `FunFamily.blocks` to `EnsembleLemmas.blocks` (`hb`) and then applies `EnsembleLemmas.ofFn_blocks_symm`;
with the restated lemma the second rewrite finds no instance (`rw` matches at reducible transparency; `EnsembleLemmas.blocks`
is a plain `def`). Q-A1. No other S2-A change reaches another job's file: all consumers of the restated headers and
changed bodies are S2-A files, and the remaining external uses of S2-A's changed lemmas are definitional (`exact`,
term-mode `have`).

**Records outside the Lean PR.** S2A-N03 (bb1-sim design r1 §2.2 dated correction, `briefs/pairings/`) and the DW-9,
DW-10, PS10 and ledger rows S2-A closes (DL-38 partial, DL-41, DL-43 promotion half, DL-46 partial, DL-47 partial, DL-48
partial, DL-51 partial, DL-55, DL-56 reader half, DL-57 promotion half, DL-59 generalization half): the stage-level
closure stays with S2-D's Stage 2 gate.

## 4. The interface S2-B, S2-C and S2-D are pinned to

S2-B/C/D are issued on the post-S2-A tip. They may rely on exactly these S2-A outputs (names and statements as in §1.1
and the TSV; any change after a ruling is re-announced in their briefs):

| S2-A output | step | used by |
|---|---|---|
| `Complexity.polyTimeComputable_iterateFind_elim` | A02 | S2-B: `GGM/Reduction.lean` (S2-SL-285..287) |
| `Ensemble.distAdv_uniform`, `indist_iff`, `samplable_iff` | A07 | S2-B: `Generators/Asymptotic/Defs.lean` (S2-SL-307, 309, 310) |
| `EnsembleLemmas.swapAux_apply` | A07 | S2-D: `CommitmentLemmas.lean` (S2-SL-340) |
| `fisherYates_def`, `permFromCoins_def` | A07 | S2-D: `EncodingPermutations.lean` (S2-SL-361, 362) |
| `owpGen_apply`, `owpPair_apply`, `owpGenNot_apply` | A08 | S2-B: `Trapdoor.lean`, `FromPermutation.lean`; S2-D: `Commitment.lean` |
| `Games.extTape`, `extTape_of_lt`, `extTape_of_not_lt`, `extTape_update` at `{C : Type*}` | A03 | S2-B: `AdaptiveCPA.extTape` and `LazySampling.extendStream` become body aliases (Q7/Q8), `LazySampling` imports `Games.Tapes` |
| `ProbComp.mul_prob_le_expect` | A04 | S2-B: `Lamport/Averaging.lean:129` (S2-RP-102) |
| `TCSlib.Cryptography.decide_singleton_eq_true` now in `Foundations/BitLists.lean` | A05 | S2-B: `TrapdoorPredictor.lean` (unchanged name) |
| `IBEScheme.sidSpec_dom_zero/one/two`, `sidSpec_rng_zero/one/two`, `zeroBits_eq_cast` (home per Q-A6) | A06 | S2-B: `BonehBoyenSecurity/Lazy.lean` (names kept, re-derived), `BonehBoyenMachine/Oracles.lean` (private copies deleted) |
| `InteractiveHandler.rU_eq`, `rZ_eq`, `rW_eq`, `rS_eq` (Q-A5) | A09 | S2-B: `BonehBoyenMachine/Words.lean` (DL-56) |
| DL-35 #1, #3, #6 done; `EnsembleLemmas.blocks` still present | A21, A25 | S2-B (#5, #7–14), S2-D (#4, `ColRepSound`, then the alias removal; #2 if Q-A1a) |
| the `PolyExpr.eval` B-only recipe and convention (Q-A9) | §1.3, §1.5 | S2-B's 22 and S2-D's 2 statement-level rows; S2-B/C/D proof-level rows |
| `PolyExpr` readers: none added; `eval_*` (`PolyExpr.lean:116–131`) suffice for every S2-A row | – | all |

Nothing in S2-B/C/D depends on J1 (the Complexity hosts) or on J2's restated headers.

## 5. Risks, ambiguities and questions

**Risks without a question.**
- **Q11 readers in a handed-off file.** `Encoding.lean` is also changed on the Arora–Barak branch; the two insertions are
  placed next to their definitions (l.125, l.153) as pure additions. Tell the handoff chat (DW10-Q11); expect a merge
  interaction at `main`.
- **Needs-check items** (18 seal fixes): each is probed first in its step (A15 `SL-089`, A16 `SL-108`, A19 `SL-280`,
  A21 `SL-155..157`, A22 `SL-204/205/208..213`, A36 `SL-164..167`). `SL-164..167` cite `glPad_f`, whose statement
  changes under Q-A3.
- **F07 readers.** S2-A's five readers without a concrete statement (`indist_iff`, `samplable_iff`, `lengthRegular_iff`,
  `sampleAll_eq`, `yaoRaw_eq`) get statements here. The other three of the plan's eight (`queryOf_eq_some_iff_decode`,
  `trialIdx_def`, `giProver_next`) are S2-B/S2-C's.
- **`yaoRaw_eq` uses `Option.elim`**, not `match`: a statement-level `match` creates a fresh matcher, which is the seal
  failure being fixed (C3-0004's `…match_1.splitter`).
- **Stale intermediate oleans within a batch.** Only additive or proof-only changes, one universe generalization
  (`Games/Tapes`, 2 downstream modules: re-check both in A03), one same-name move and three deletions of uncalled
  lemmas occur before a replay; the D1/D2 replays are the authority. Strict alternative: re-check the "path" modules.
- **Line drift for S2-B/C/D.** Their briefs re-locate on the post-S2-A tip (TrapdoorPredictor −4 lines; Ensembles,
  EnsemblesLemmas grow).
- **Seal targets.** Strict-only failures are reported, not fixed (Q3); W5 `local irreducible` lines are reported
  separately; `IterateFind` is re-sealed (F-01).
- **Lean slots.** Local hosts: at most 3 Lean processes across all jobs; the D1 replay (776 modules) competes with
  the S2-B/C/D Codex replays only after S2-A merges, since they are pinned on its tip.

**Questions for Seyoon** (recommended option first).

- **Q-A1. DL-35 #2 (`EnsembleLemmas.ofFn_blocks_symm` statement) breaks `ZeroKnowledge/Commitment.lean:852–853` (S2-D).**
  - **(a) Recommended:** move S2-BK-02 to S2-D, which owns `Commitment.lean` and removes the aliases in
    `EnsemblesLemmas.lean` anyway; S2-D changes the statement and deletes the `hb` rewrite in the same commit. S2-A keeps
    the proof-only S2-RP-030.
  - (b) S2-A makes the change and the two-line proof fix in `Commitment.lean` (crossing into S2-D's file; S2-D rebases).
  - (c) Keep the old statement and add a `FunFamily.blocks` corollary (a new duplicate; DL-35 then closes with a note).
- **Q-A2. 15 definitions among the SEAL-B-ONLY "proof-level" rows need body changes** (§1.4: `owfFamily`,
  `Ensemble.copies`, `glPad`, `glBit`, `glInverter`, `glPad_inEquiv`, `glPad_outEquiv`, `HardCoreCollection.glPad`,
  `oddCoins`, `FunFamily.prod`, `PermFamily.toFunFamily`, `toFunFamily_codEquiv`, `toFunFamily_domEquiv`, `fmult`,
  `plantFactor`).
  - **(a) Recommended:** approve them as Q8 freeze exceptions of Q7's kind: definitional bodies, casts only through
    `PolyExpr.eval_*`/published `*_eval` readers, each listed and checked by the gate (decls2 CHANGED, with an `rfl`
    probe old-body = new-body in the evidence).
  - (b) Leave the bodies and record their coe-B failures as accepted residue (the Stage 2 target "no seal failure in a
    touched file" is then not met for 7 owners).
  - (c) Restate them through new length-typed helper definitions (more API, more churn).
- **Q-A3. Three more headers fail under seal B** (`FunFamily.glPad_f`, `glBit_append`, private `invProbAt_reduction_ge`;
  STAGE2 class, not in F01's 51).
  - **(a) Recommended:** grant them as Q8 freeze exceptions of the same kind, restated as in §1.3 rows 12–14 (the
    first two through the published `glPad_inEquiv`/`glPad_outEquiv`, which makes `glBit_append` equal to the existing
    `glBit_equiv`; keep both names, the old one re-proved from the new).
  - (b) As (a), but retire the now-duplicate `glPad_f_equiv`/`glBit_equiv` (two REMOVED in decls2).
  - (c) Leave the three headers and record the residue.
- **Q-A4. Q11's `Turing.CodeTM.toFinTM_tm` cannot be stated as a usable equation** (`M.toFinTM.tm = M.tm` is
  dependent-typed).
  - **(a) Recommended:** add `CodeTM.toFinTM_computesInTime_iff` (the run form, §1.1) as the Q11 reader instead of the
    name `toFinTM_tm`; still one pure insertion.
  - (b) The same statement under the ruled name `toFinTM_tm`.
  - (c) The literal pair `toFinTM_State` (`= Fin (numStates + 1)`, `rfl`) and `toFinTM_tm : HEq M.toFinTM.tm M.tm`, with
    `Universal.lean` consuming the HEq (probe needed).
- **Q-A5. DL-56's reader is needed** (no `_eq` readers for `InteractiveHandler.rU/rZ/rW/rS`).
  - **(a) Recommended:** S2-A adds `rU_eq`, `rZ_eq`, `rW_eq`, `rS_eq` in `Games/Efficiency.lean` (A09, additive);
    S2-B re-points `BB1Machine.poly_rU…`.
  - (b) S2-B adds them (S2-B would then edit `Games/Efficiency`, which no other job touches).
  - (c) `BB1Machine.rU := InteractiveHandler.rU` etc. as Q7 body aliases, no reader.
- **Q-A6. Home of `zeroBits_eq_cast`** (about `Games.zeroBits`, not IBE-specific).
  - **(a) Recommended:** as ruled (DL-57, bb1-sim fill Q1): `IBEScheme.zeroBits_eq_cast` in `IdentityBased/Defs.lean`,
    with a docstring saying it is generic glue.
  - (b) `Games.zeroBits_eq_cast` in `Games/BitCodec.lean` beside `zeroBits` (the natural home; deeper rebuild).
- **Q-A7. S2-RP-088 (`DyadicUniform`'s three `bitsTo*_uniform`, flagged "optional; near-copies" in the Stage 1 table).**
  - **(a) Recommended:** no change; record as a CS1-Q10 near-relative note.
  - (b) Re-derive the three from `FinDist.map_uniform_equiv` (~12 lines, A31).
- **Q-A8. `PermFamily.toFunFamily_f` is `@[simp]`;** its restated right-hand side goes through `toFunFamily_codEquiv`/`domEquiv`.
  - **(a) Recommended:** keep `@[simp]` (consumers found only in S2-A files) and probe the downstream `simp` calls in A24.
  - (b) Drop `@[simp]` (a further attribute change to list).
- **Q-A9. Convention for every statement-level restatement in Stage 2** (S2-A's 14; also S2-B's 22 and S2-D's 2).
  - **(a) Recommended:** binders at the family's own `PolyExpr` type, so left-hand sides stay matchable; concrete
    lengths through `Fin.cast` of published `*_eval` readers or published equivalences.
  - (b) Keep the book-facing binders (`Fin (2 * n)`, `Fin n`) and cast at the family application (left-hand sides no
    longer match plain uses by `rw`).
- **Q-A10. Validation.**
  - **(a) Recommended:** per step, check the changed files (and, for statement-visible steps, their direct importers)
    with `lean_check_tree.sh`; one replay per batch (D1: 776 modules; D2: 339); seals on the batch's owners; one PR
    for S2-A carrying the 38 step commits, one Codex gate.
  - (b) Strict: also re-check each step's "path" modules before its own files.
  - (c) Two PRs (D1, D2), each with its own gate.
- **Q-A11. Order of DL-55's move against S2-B's `TrapdoorPredictor` seal fixes.**
  - **(a) Recommended:** the move stays in S2-A (A05, atomic, ruled J0); S2-B's brief re-locates its two rows.
  - (b) Move DL-55 to S2-B (it then owns `TrapdoorPredictor`, `Foundations/BitLists` and `Pairing/Assumptions`).

Steps that need no ruling: A02–A05, A07, A08, A10–A22, A26, A27, A32–A34, A38. Waiting: A01 (Q-A4), A06 (Q-A6),
A09 (Q-A5), A31 (Q-A7), A23–A25, A28–A30, A35–A37 (Q-A2, Q-A3, Q-A9; A24 also Q-A8). Q-A1, Q-A10 and Q-A11 shape the
job but block no step.

**Ready to run** — A02–A05, A07, A08 and J1 (A10–A18) can start on the tip now; the rest after Q-A1 to Q-A11.
