/-
Copyright (c) 2026 Seyoon Ragavan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Seyoon Ragavan
-/
import TCSlib.Complexity.Formulas.CNFEncoding
import TCSlib.Complexity.ClassNP.NP
import TCSlib.Complexity.ClassNP.Reductions
import Mathlib.Tactic.FinCases
import Mathlib.Data.List.MinMax

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# SAT and 3SAT

[AB09, §2.3.1]: `SAT` is the language of (strings representing) satisfiable CNF
formulas, `3SAT` its restriction to 3CNF formulas (at most three literals per
clause). This module defines both over the audited serialization layer, states
their membership in `NP`, and states [AB09, Lemma 2.14] (`SAT ≤ₚ 3SAT`) — the
(b) half of the Cook-Levin proof plan, whose (a) half (Lemma 2.11, `SAT` is
`NP`-hard) is phase-4 material.

## Design and deviations from [AB09]

* **Strings, not formulas, are the language elements**: membership goes through
  the total `Std.Sat.CNF.decode` ([AB09, footnote 3]). With the fallback being
  the empty formula — satisfiable, and vacuously 3CNF — **every non-well-formed
  string lies in `SAT` and in `3SAT`**. [AB09] declares the fallback choice
  immaterial, and every stated result survives any fixed fallback — but not
  "uniformly": each language's malformed-input branch follows **its own
  predicate** on the fallback (a satisfiable fallback of width four would put
  the non-well-formed strings in `SAT` and out of `3SAT` — round-1 audit,
  finding 5), and the Lemma-2.14 reduction maps a non-well-formed input to the
  serialization of the **transformed** fallback, which keeps the reduction
  equivalence whatever the fixed choice.
* **`TAUTOLOGY` and [AB09, Example 2.21] are deferred to phase 4** (plan
  decision log): [AB09]'s `TAUTOLOGY` ranges over general Boolean formulas, and
  its coNP-hardness reduction negates the Cook-Levin CNF into a **DNF** — while
  the CNF-restricted tautology language is polynomial-time decidable (a CNF is
  a tautology iff every clause contains a complementary literal pair), i.e. it
  is **not** [AB09]'s language. The faithful carrier (the DNF dual layer) and
  the hardness half's prerequisite (Lemma 2.11) both belong to phase 4, so the
  whole package moves there rather than stating a wrong-language definition
  here.

## Main definitions

* `Complexity.SAT` — satisfiable CNF strings. [AB09, §2.3.1]
* `Complexity.SAT3` — satisfiable 3CNF strings. [AB09, §2.3.1]

## Main results

* `Complexity.SAT_mem_NP`, `Complexity.SAT3_mem_NP` — the assignment is the
  certificate. [AB09, Theorem 2.10, membership part]
* `Complexity.SAT_reducible_SAT3` — clause splitting with fresh variables.
  [AB09, Lemma 2.14]

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§2.3.1, pp. 44-45; Theorem 2.10, p. 45;
  Lemma 2.14, p. 48 with §2.3.5, pp. 50-51.)
-/

namespace Complexity

open Std.Sat (CNF)
open Turing

/-- **The language `SAT`** [AB09, §2.3.1]: binary strings whose decoded CNF
formula is satisfiable. Decoding is total ([AB09, footnote 3]), with the empty —
satisfiable — formula as fallback, so every non-well-formed string is in `SAT`
(see the deviations list). -/
def SAT : Language Bool :=
  {x | (CNF.decode x).Satisfiable}

/-- **The language `3SAT`** [AB09, §2.3.1]: binary strings whose decoded formula
is a satisfiable 3CNF — every clause with at most three literals. The fallback
formula has no clauses, so non-well-formed strings are in `3SAT` as well. -/
def SAT3 : Language Bool :=
  {x | (CNF.decode x).WidthAtMost 3 ∧ (CNF.decode x).Satisfiable}

/-! **Epoch-3 fill note.** The private verifier layer below uses the audited
`(1,1)` split. Syntax validation is a separate complete pass; neither width
nor evaluation is allowed to reject an incompletely parsed prefix. -/

/-- The finite assignment carried by a certificate, with the agreed default. -/
private def satAssignment (u : List Bool) : ℕ → Bool := fun v => u.getD v false

/-- Restricting a total assignment to the prescribed certificate length keeps
every variable used by the decoded formula. [AB09, Theorem 2.10, membership]

**Proof sketch.** Tabulate the first `|x|+1` bits. The decoded variable bound
puts each relevant index inside the tabulation; evaluation congruence applies. -/
private lemma sat_certificate (x : List Bool) :
    (CNF.decode x).Satisfiable ↔ ∃ u : List Bool,
      u.length = x.length + 1 ∧ (CNF.decode x).eval (satAssignment u) = true := by
  constructor
  · rintro ⟨a, ha⟩
    let u := List.ofFn (fun i : Fin (x.length + 1) => a i.val)
    refine ⟨u, List.length_ofFn, ?_⟩
    rw [← ha]
    apply eval_congr_of_lt_numVars
    intro v hv
    have hlt : v < x.length + 1 := Nat.lt_of_lt_of_le hv
      (Nat.le_trans (CNF.numVars_decode_le x) (Nat.le_succ _))
    simp only [satAssignment, u, List.getD_eq_getElem?_getD, List.getElem?_ofFn,
      dif_pos hlt, Option.getD_some]
  · rintro ⟨u, _, hu⟩
    exact ⟨satAssignment u, hu⟩

/-- A successful catalog split has the exact odd-length equation. -/
private lemma sat_split_some (N i : ℕ) (h : solveSplit 1 1 N = some i) :
    i + (i + 1) = N := by
  have he := List.find?_some h
  simpa [Nat.pow_one] using he

/-- The unique solution is found, including `N=1`, `i=0`. -/
private lemma sat_split_exists (N i : ℕ) (h : i + (i + 1) = N) :
    solveSplit 1 1 N = some i := by
  cases hs : solveSplit 1 1 N with
  | none =>
    have hn := List.find?_eq_none.mp hs i (by simp <;> omega)
    simp [h] at hn
  | some j =>
    have hj := sat_split_some N j hs
    congr 1
    omega

/-- Even total lengths are rejected by the exact split search. -/
private lemma sat_split_even (N : ℕ) (h : N % 2 = 0) :
    solveSplit 1 1 N = none := by
  cases hs : solveSplit 1 1 N with
  | none => rfl
  | some i => have hi := sat_split_some N i hs <;> omega

/-- Boolean width test; repeated literals count as distinct occurrences. -/
private def satWidth (φ : CNF ℕ) : Bool := φ.all fun C => decide (C.length ≤ 3)

/-- The Boolean width scan is precisely the frozen formula predicate. -/
private lemma satWidth_spec (φ : CNF ℕ) :
    satWidth φ = true ↔ φ.WidthAtMost 3 := by
  simp [satWidth, CNF.WidthAtMost]

/-- The total mathematical verifier, with explicit rejection on split failure.
`decode` completes the syntax check before either semantic test is applied. -/
private def satVerdict (three : Bool) (z : List Bool) : Bool :=
  match solveSplit 1 1 z.length with
  | none => false
  | some i =>
      let φ := CNF.decode (z.take i)
      (!three || satWidth φ) && φ.eval (satAssignment (z.drop i))

/-- Verifier languages for the two prescribed `(1,1)` witnesses. -/
private def satVerifier (three : Bool) : Language Bool := {z | satVerdict three z = true}

/-- A correctly sized concatenation is recovered literally by the verifier. -/
private lemma satVerdict_append (three : Bool) (x u : List Bool)
    (hu : u.length = x.length + 1) :
    satVerdict three (x ++ u) =
      ((!three || satWidth (CNF.decode x)) && (CNF.decode x).eval (satAssignment u)) := by
  unfold satVerdict
  rw [sat_split_exists (x ++ u).length x.length (by simp [hu])]
  simp

/-- The SAT certificate equivalence, with exactly the audited `n+1` bits. -/
private lemma sat_verifier_equiv (x : List Bool) :
    x ∈ SAT ↔ ∃ u : List Bool, u.length = x.length + 1 ∧ x ++ u ∈ satVerifier false := by
  rw [show x ∈ SAT ↔ (CNF.decode x).Satisfiable from Iff.rfl, sat_certificate]
  apply exists_congr
  intro u
  apply and_congr_right
  intro hu
  change _ ↔ satVerdict false (x ++ u) = true
  simp [satVerdict_append false x u hu]

/-- Width depends only on the instance, so the same certificate suffices for 3SAT. -/
private lemma sat3_verifier_equiv (x : List Bool) :
    x ∈ SAT3 ↔ ∃ u : List Bool, u.length = x.length + 1 ∧ x ++ u ∈ satVerifier true := by
  change (CNF.decode x).WidthAtMost 3 ∧ (CNF.decode x).Satisfiable ↔ _
  rw [sat_certificate]
  constructor
  · rintro ⟨hw, u, hu, he⟩
    refine ⟨u, hu, ?_⟩
    change satVerdict true (x ++ u) = true
    simp [satVerdict_append true x u hu, (satWidth_spec _).mpr hw, he]
  · rintro ⟨u, hu, hv⟩
    change satVerdict true (x ++ u) = true at hv
    have hh : satWidth (CNF.decode x) = true ∧
        (CNF.decode x).eval (satAssignment u) = true := by
      simpa [satVerdict_append true x u hu] using hv
    exact ⟨(satWidth_spec _).mp hh.1, u, hu, hh.2⟩

/-- The unary scanner partitions its input into the counted run and its suffix. -/
private lemma sat_takeTrues_repr (x : List Bool) :
    List.replicate (CNF.takeTrues x).1 true ++ (CNF.takeTrues x).2 = x := by
  induction x with
  | nil => rfl
  | cons b x ih =>
    cases b with
    | false => rfl
    | true => simpa [CNF.takeTrues, List.replicate_succ] using congrArg (true :: ·) ih

/-- A successful literal parse reconstructs exactly the consumed input. -/
private lemma sat_parseLit_repr {x r : List Bool} {ℓ : Std.Sat.Literal ℕ}
    (h : CNF.parseLit x = some (ℓ, r)) : x = CNF.serializeLit ℓ ++ r := by
  have ht := sat_takeTrues_repr x
  unfold CNF.parseLit at h
  split at h
  · cases h
  · rename_i k b rest he
    cases h
    simpa [he, CNF.serializeLit, List.append_assoc] using ht.symm
  · cases h

/-- Clause parsing reconstructs its terminator as well as every literal.

**Proof sketch.** Induct on fuel. The leading zero case succeeds even at
zero fuel. Otherwise invert both successful subparses and concatenate their
reconstruction equalities; no premature end of the input can succeed. -/
private lemma sat_parseClause_repr {fuel : ℕ} {x r : List Bool} {C : CNF.Clause ℕ}
    (h : CNF.parseClause fuel x = some (C, r)) : x = CNF.serializeClause C ++ r := by
  induction fuel generalizing x C r with
  | zero =>
    cases x with
    | nil => cases h
    | cons b s =>
      cases b with
      | false => cases h; rfl
      | true => cases h
  | succ fuel ih =>
    cases x with
    | nil => cases h
    | cons b s =>
      cases b with
      | false => cases h; rfl
      | true =>
        cases hl : CNF.parseLit (true :: s) with
        | none => simp [CNF.parseClause, hl] at h
        | some p =>
          obtain ⟨ℓ, t⟩ := p
          cases hc : CNF.parseClause fuel t with
          | none => simp [CNF.parseClause, hl, hc] at h
          | some p =>
            obtain ⟨D, v⟩ := p
            simp only [CNF.parseClause, hl, hc, Option.some.injEq, Prod.mk.injEq] at h
            rcases h with ⟨rfl, rfl⟩
            rw [sat_parseLit_repr hl, ih hc]
            simp [CNF.serializeClause, List.append_assoc]

/-- Formula parsing reconstructs every clause marker and the final terminator.

**Proof sketch.** Induct on fuel, retaining the unconsumed suffix. A clause
marker spends one unit of fuel before the clause and formula subparses.
The leading zero case works independently of the remaining fuel. -/
private lemma sat_parseClauses_repr {fuel : ℕ} {x r : List Bool} {φ : CNF ℕ}
    (h : CNF.parseClauses fuel x = some (φ, r)) : x = CNF.serialize φ ++ r := by
  induction fuel generalizing x φ r with
  | zero =>
    cases x with
    | nil => cases h
    | cons b s =>
      cases b with
      | false => cases h; rfl
      | true => cases h
  | succ fuel ih =>
    cases x with
    | nil => cases h
    | cons b s =>
      cases b with
      | false => cases h; rfl
      | true =>
        cases hc : CNF.parseClause fuel s with
        | none => simp [CNF.parseClauses, hc] at h
        | some p =>
          obtain ⟨C, t⟩ := p
          cases ht : CNF.parseClauses fuel t with
          | none => simp [CNF.parseClauses, hc, ht] at h
          | some p =>
            obtain ⟨ψ, v⟩ := p
            simp only [CNF.parseClauses, hc, ht, Option.some.injEq, Prod.mk.injEq] at h
            rcases h with ⟨rfl, rfl⟩
            rw [sat_parseClause_repr hc, ih ht]
            simp [CNF.serialize, CNF.serializeClause, List.append_assoc]

/-- Exact-consumption parsing is inverse serialization on every successful input. -/
private lemma sat_parse_repr {x : List Bool} {φ : CNF ℕ}
    (h : CNF.parse x = some φ) : x = CNF.serialize φ := by
  unfold CNF.parse at h
  split at h
  · rename_i ψ hp
    cases h
    simpa using sat_parseClauses_repr hp
  · cases h

/-- The six LL(1) positions: formula, clause, unary index, polarity, exact
end, and error. The end position becomes error on any trailing bit. -/
private def satSyntaxStep (q : Fin 6) (b : Bool) : Fin 6 :=
  match q.val with
  | 0 => if b then 1 else 4
  | 1 => if b then 2 else 0
  | 2 => if b then 2 else 3
  | 3 => 1
  | _ => 5

/-- Residual grammar at each finite-control position. Unary indices remain
unbounded strings; the finite control stores only their grammar position. -/
private def satSyntaxSuffix (q : Fin 6) (x : List Bool) : Prop :=
  match q.val with
  | 0 => ∃ φ : CNF ℕ, x = CNF.serialize φ
  | 1 => ∃ (C : CNF.Clause ℕ) (φ : CNF ℕ), x = CNF.serializeClause C ++ CNF.serialize φ
  | 2 => ∃ (v : ℕ) (b : Bool) (C : CNF.Clause ℕ) (φ : CNF ℕ),
      x = List.replicate v true ++ [false, b] ++ CNF.serializeClause C ++ CNF.serialize φ
  | 3 => ∃ (b : Bool) (C : CNF.Clause ℕ) (φ : CNF ℕ),
      x = b :: (CNF.serializeClause C ++ CNF.serialize φ)
  | 4 => x = []
  | _ => False

/-- Each transition consumes exactly one grammar bit.

**Proof sketch.** Invert the first clause, literal, or unary-run constructor
as appropriate. Formula and clause zero-markers are distinct states; the
polarity state consumes its bit unconditionally. No bit can follow the
exact-end state, which is how trailing garbage forces the fallback. -/
private lemma satSyntaxSuffix_cons (q : Fin 6) (b : Bool) (x : List Bool) :
    satSyntaxSuffix q (b :: x) ↔ satSyntaxSuffix (satSyntaxStep q b) x := by
  fin_cases q <;> cases b
  · change (∃ φ, false :: x = CNF.serialize φ) ↔ x = []
    constructor
    · rintro ⟨φ, h⟩; cases φ <;> simpa [CNF.serialize] using h
    · rintro rfl; exact ⟨[], rfl⟩
  · change (∃ φ, true :: x = CNF.serialize φ) ↔
      ∃ C φ, x = CNF.serializeClause C ++ CNF.serialize φ
    constructor
    · rintro ⟨φ, h⟩
      cases φ with
      | nil => simp [CNF.serialize] at h
      | cons C φ => exact ⟨C, φ, by simpa [CNF.serialize, List.append_assoc] using h⟩
    · rintro ⟨C, φ, rfl⟩
      exact ⟨C :: φ, by simp [CNF.serialize, List.append_assoc]⟩
  · change (∃ C φ, false :: x = CNF.serializeClause C ++ CNF.serialize φ) ↔
      ∃ φ, x = CNF.serialize φ
    constructor
    · rintro ⟨C, φ, h⟩
      cases C with
      | nil => exact ⟨φ, by simpa [CNF.serializeClause] using h⟩
      | cons ℓ C => simp [CNF.serializeClause, CNF.serializeLit, List.replicate_succ] at h
    · rintro ⟨φ, rfl⟩; exact ⟨[], φ, rfl⟩
  · change (∃ C φ, true :: x = CNF.serializeClause C ++ CNF.serialize φ) ↔
      ∃ v b C φ, x = List.replicate v true ++ [false, b] ++
        CNF.serializeClause C ++ CNF.serialize φ
    constructor
    · rintro ⟨C, φ, h⟩
      cases C with
      | nil => simp [CNF.serializeClause] at h
      | cons ℓ C =>
        exact ⟨ℓ.1, ℓ.2, C, φ, by simpa [CNF.serializeClause, CNF.serializeLit,
          List.replicate_succ, List.append_assoc] using h⟩
    · rintro ⟨v, b, C, φ, rfl⟩
      exact ⟨(v, b) :: C, φ, by simp [CNF.serializeClause, CNF.serializeLit,
        List.replicate_succ, List.append_assoc]⟩
  · change (∃ v b C φ, false :: x = List.replicate v true ++ [false, b] ++
      CNF.serializeClause C ++ CNF.serialize φ) ↔
        ∃ b C φ, x = b :: (CNF.serializeClause C ++ CNF.serialize φ)
    constructor
    · rintro ⟨v, b, C, φ, h⟩
      cases v with
      | zero => exact ⟨b, C, φ, by simpa [List.append_assoc] using h⟩
      | succ v => simp [List.replicate_succ] at h
    · rintro ⟨b, C, φ, rfl⟩; exact ⟨0, b, C, φ, by simp⟩
  · change (∃ v b C φ, true :: x = List.replicate v true ++ [false, b] ++
      CNF.serializeClause C ++ CNF.serialize φ) ↔
        ∃ v b C φ, x = List.replicate v true ++ [false, b] ++
          CNF.serializeClause C ++ CNF.serialize φ
    constructor
    · rintro ⟨v, b, C, φ, h⟩
      cases v with
      | zero => simp at h
      | succ v => exact ⟨v, b, C, φ, by simpa [List.replicate_succ] using h⟩
    · rintro ⟨v, b, C, φ, rfl⟩
      exact ⟨v + 1, b, C, φ, by simp [List.replicate_succ]⟩
  · change (∃ b C φ, false :: x = b :: (CNF.serializeClause C ++ CNF.serialize φ)) ↔
      ∃ C φ, x = CNF.serializeClause C ++ CNF.serialize φ
    simp
  · change (∃ b C φ, true :: x = b :: (CNF.serializeClause C ++ CNF.serialize φ)) ↔
      ∃ C φ, x = CNF.serializeClause C ++ CNF.serialize φ
    simp
  all_goals simp [satSyntaxSuffix, satSyntaxStep]

/-- At end of input, exactly the exact-end grammar state accepts. -/
private lemma satSyntaxSuffix_nil (q : Fin 6) : satSyntaxSuffix q [] ↔ q = 4 := by
  fin_cases q <;> simp [satSyntaxSuffix, CNF.serialize, CNF.serializeClause,
    List.append_eq_nil_iff]

/-- The complete finite-state scan recognizes precisely the residual grammar. -/
private lemma satSyntaxSuffix_run (q : Fin 6) (x : List Bool) :
    satSyntaxSuffix q x ↔ x.foldl satSyntaxStep q = 4 := by
  induction x generalizing q with
  | nil => exact satSyntaxSuffix_nil q
  | cons b x ih => rw [satSyntaxSuffix_cons, List.foldl_cons, ← ih]

/-- Boolean result of the complete syntax pass. -/
private def satSyntax (x : List Bool) : Bool := decide (x.foldl satSyntaxStep 0 = 4)

/-- The machine grammar and the audited parser agree on every string, including
empty input, unfinished literals, and trailing garbage.

**Proof sketch.** The residual-language invariant identifies scan acceptance
with the range of serialization. Successful parsing reconstructs its entire
input, and the existing parser round trip proves the converse. -/
private lemma satSyntax_spec (x : List Bool) : satSyntax x = (CNF.parse x).isSome := by
  apply Bool.eq_iff_iff.mpr
  simp only [satSyntax, decide_eq_true_eq]
  rw [← satSyntaxSuffix_run]
  change (∃ φ, x = CNF.serialize φ) ↔ (CNF.parse x).isSome = true
  constructor
  · rintro ⟨φ, rfl⟩; simp [CNF.parse_serialize]
  · intro h
    cases hp : CNF.parse x with
    | none => simp [hp] at h
    | some φ => exact ⟨φ, sat_parse_repr hp⟩

/-- One-way finite-state scanners use no work tapes and emit only the final
verdict, after inspecting the right boundary. -/
private def satScanTM {S : Type} [Fintype S] [DecidableEq S]
    (step : S → Bool → S) (start : S) (accept : S → Bool) : FinTM Bool where
  k := 0
  State := S
  tm := {
    q₀ := start
    tr := fun q inp _ => match inp with
      | some b => ⟨.pos, Fin.elim0, none, some (step q b)⟩
      | none => ⟨0, Fin.elim0, some (accept q), none⟩ }

/-- Scanner configuration just before input symbol `i`, with empty output. -/
private def satScanCfg {S : Type} (x : List Bool) (q : S) (i : ℕ)
    (hi : i ≤ x.length) : Cfg 0 Bool S x :=
  ⟨some q, ⟨i + 1, by omega⟩, Fin.elim0, Fin.elim0, []⟩

/-- One real scanner step consumes one input symbol silently. -/
private lemma satScan_step {S : Type} [Fintype S] [DecidableEq S]
    (step : S → Bool → S) (start : S) (accept : S → Bool)
    (x : List Bool) (q : S) (i : ℕ) (hi : i < x.length) :
    (satScanTM step start accept).tm.step (satScanCfg x q i (by omega)) =
      satScanCfg x (step q x[i]) (i + 1) (by omega) := by
  have hin := inputSymbolInner (cfg := satScanCfg x q i (by omega)) i
    (by simp [satScanCfg, Nat.add_comm]) hi
  unfold MultiTapeTM.step
  change (((satScanTM step start accept).tm.tr q _ _).apply _) = _
  rw [hin]
  apply Cfg.ext_zero_tapes
  · rfl
  · exact moveInputPos_pos_of_ne_right _ (by simp [satScanCfg] <;> omega)
  · rfl

/-- A suffix scan consumes every remaining bit and then emits one verdict.

**Proof sketch.** Induct on the suffix. The empty case reads the right blank;
the nonempty case is one silent step followed by the induction hypothesis.
The initial output is empty and no earlier step emits. -/
private lemma satScan_run {S : Type} [Fintype S] [DecidableEq S]
    (step : S → Bool → S) (start : S) (accept : S → Bool)
    (x rest : List Bool) : ∀ pre (hx : x = pre ++ rest) (q : S),
      ((satScanTM step start accept).tm.runFrom
        (satScanCfg x q pre.length (by simp [hx])) (rest.length + 1)).state = none ∧
      ((satScanTM step start accept).tm.runFrom
        (satScanCfg x q pre.length (by simp [hx])) (rest.length + 1)).output =
          [accept (rest.foldl step q)] := by
  induction rest with
  | nil =>
    intro pre hx q
    subst x
    simp [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.step, satScanTM,
      satScanCfg, Cfg.inputSymbol, Action.apply]
  | cons b rest ih =>
    intro pre hx q
    have hi : pre.length < x.length := by simp [hx]
    have hget : x[pre.length] = b := by simp [hx]
    have hs := satScan_step step start accept x q pre.length hi
    rw [hget] at hs
    simp only [List.length_cons, MultiTapeTM.runFrom_succ_eq_step]
    rw [hs]
    simpa only [List.length_append, List.length_singleton, List.foldl_cons] using
      ih (pre ++ [b]) (by simpa [List.append_assoc] using hx) (step q b)

/-- Every such scanner has the exact `n+1` bound. -/
private lemma satScan_computes {S : Type} [Fintype S] [DecidableEq S]
    (step : S → Bool → S) (start : S) (accept : S → Bool) :
    (satScanTM step start accept).ComputesFunInTime
      (fun x => [accept (x.foldl step start)]) (fun n => n + 1) := by
  intro x
  apply (FinTM.computesInTime_iff _ _ _ _).mpr
  have hinit : (satScanTM step start accept).tm.initCfg x =
      satScanCfg x start 0 (Nat.zero_le _) := Cfg.ext_zero_tapes rfl rfl rfl
  rw [hinit]
  exact satScan_run step start accept x x [] rfl start

/-- The complete CNF syntax pass is realized by an actual finite machine.
The result concerns every input, not merely serialized formulas. -/
private lemma satSyntax_poly : PolyTimeComputable (fun x => [satSyntax x]) := by
  refine ⟨satScanTM satSyntaxStep 0 (fun q => decide (q = 4)), 1, 1, ?_⟩
  simpa only [Nat.pow_one, Nat.one_mul, satSyntax] using
    satScan_computes satSyntaxStep 0 (fun q => decide (q = 4))

/-- Administrative states, or a streaming phase (formula, clause, index,
polarity, rewind) with formula/clause truth bits and a doubled-bit skip flag. -/
private abbrev SatEvalControl := Fin 4 ⊕ (Fin 5 × Bool × Bool × Bool)

/-- A semantic phase, with the input poised at a doubled bit unless skipping. -/
private def satEvalQ (q : Fin 5) (a c skip : Bool) : SatEvalControl :=
  .inr (q, a, c, skip)

/-- Administrative evaluation actions preserve all tape contents and move only
the input head and the captured-certificate head. -/
private def satEvalAction (M : FinTM Bool) (m d : SignType) (b : Option Bool)
    (q : Option SatEvalControl) : Action (M.k + 1) Bool (M.State ⊕ SatEvalControl) :=
  ⟨m, fun i => (none, if i.val < M.k then 0 else d), b, q.map Sum.inr⟩

/-- Capture the certificate extractor, rewind, and evaluate a previously
validated doubled formula. No physical output occurs before the verdict.
Unary index walks and their rewinds take linear time in the literal encoding.
[AB09, Theorem 2.10, membership] -/
private def satEvalTM (M : FinTM Bool) : FinTM Bool where
  k := M.k + 1
  State := M.State ⊕ SatEvalControl
  tm := {
    q₀ := .inl M.tm.q₀
    tr := fun s inp work => match s with
    | .inl q => captureAction Sum.inl (.inr (.inl 0))
        (M.tm.tr q inp fun i => work i.castSucc)
    | .inr (.inl q) => match q.val with
      | 0 => FinTM.controlAction .neg (some (.inr (.inl 1)))
      | 1 => match inp with
        | some _ => FinTM.controlAction .neg (some (.inr (.inl 1)))
        | none => FinTM.controlAction .pos (some (.inr (.inl 2)))
      | 2 => satEvalAction M 0 .neg none (some (.inl 3))
      | _ => match work (Fin.last M.k) with
        | some _ => satEvalAction M 0 .neg none (some (.inl 3))
        | none => satEvalAction M 0 .pos none (some (satEvalQ 0 true false false))
    | .inr (.inr (q, a, c, skip)) =>
      if skip then satEvalAction M .pos 0 none (some (satEvalQ q a c false))
      else if q = 4 then
        match work (Fin.last M.k) with
        | some _ => satEvalAction M 0 .neg none (some (satEvalQ 4 a c false))
        | none => satEvalAction M 0 .pos none (some (satEvalQ 1 a c false))
      else match inp with
        | none => satEvalAction M 0 0 (some false) none
        | some b => match q.val with
          | 0 => if b then satEvalAction M .pos 0 none (some (satEvalQ 1 a false true))
            else satEvalAction M 0 0 (some a) none
          | 1 => if b then satEvalAction M .pos 0 none (some (satEvalQ 2 a c true))
            else satEvalAction M .pos 0 none (some (satEvalQ 0 (a && c) false true))
          | 2 => if b then satEvalAction M .pos .pos none (some (satEvalQ 2 a c true))
            else satEvalAction M .pos 0 none (some (satEvalQ 3 a c true))
          | _ => satEvalAction M .pos 0 none
              (some (satEvalQ 4 a (c || decide (work (Fin.last M.k) = some b)) true)) }

/-- The saved extractor bank and the certificate buffer during evaluation. -/
private def satEvalCfg (M : FinTM Bool) {w : List Bool}
    (saved : Cfg M.k Bool M.State w) (u : List Bool) (q : SatEvalControl)
    (i : ℕ) (hi : i ≤ w.length) (j : ℤ) : Cfg (M.k + 1) Bool (satEvalTM M).State w :=
  ⟨some (.inr q), ⟨i + 1, by omega⟩,
    fun t => if h : t.val < M.k then saved.workTapes ⟨t, h⟩ else FinTM.bufferTape u,
    fun t => if h : t.val < M.k then saved.workTapePos ⟨t, h⟩ else j, []⟩

/-- The input read does not depend on the saved extractor bank. -/
private lemma satEvalCfg_input (M : FinTM Bool) {w : List Bool}
    (saved : Cfg M.k Bool M.State w) (u : List Bool) (q : SatEvalControl)
    (i : ℕ) (hi : i ≤ w.length) (j : ℤ) :
    (satEvalCfg M saved u q i hi j).inputSymbol = w[i]? :=
  FinTM.inputSymbol_at _ i hi rfl

/-- The last work head reads exactly the immutable certificate buffer. -/
private lemma satEvalCfg_work (M : FinTM Bool) {w : List Bool}
    (saved : Cfg M.k Bool M.State w) (u : List Bool) (q : SatEvalControl)
    (i : ℕ) (hi : i ≤ w.length) (j : ℤ) :
    (satEvalCfg M saved u q i hi j).workTapeSymbols (Fin.last M.k) =
      FinTM.bufferTape u j := by
  simp [satEvalCfg, Cfg.workTapeSymbols]

/-- A live administrative action preserves both the saved bank and output. -/
private lemma satEvalAction_apply (M : FinTM Bool) {w : List Bool}
    (saved : Cfg M.k Bool M.State w) (u : List Bool) (q q' : SatEvalControl)
    (i i' : ℕ) (hi : i ≤ w.length) (hi' : i' ≤ w.length) (j j' : ℤ)
    (m d : SignType)
    (hm : moveInputPos (⟨i + 1, by omega⟩ : Fin (w.length + 2)) m = ⟨i' + 1, by omega⟩)
    (hd : j + d.cast = j') :
    (satEvalAction M m d none (some q')).apply (satEvalCfg M saved u q i hi j) =
      satEvalCfg M saved u q' i' hi' j' := by
  refine Cfg.ext rfl hm rfl ?_ rfl
  funext t
  by_cases ht : t.val < M.k
  · simp [satEvalAction, satEvalCfg, Action.apply, ht]
  · simpa [satEvalAction, satEvalCfg, Action.apply, ht] using hd

/-- The second bit of a doubled input symbol is skipped silently. -/
private lemma satEval_skip (M : FinTM Bool) {w : List Bool}
    (saved : Cfg M.k Bool M.State w) (u : List Bool) (q : Fin 5) (a c : Bool)
    (i : ℕ) (hi : i < w.length) (j : ℤ) :
    (satEvalTM M).tm.step (satEvalCfg M saved u (satEvalQ q a c true) i (by omega) j) =
      satEvalCfg M saved u (satEvalQ q a c false) (i + 1) (by omega) j := by
  unfold MultiTapeTM.step
  change (satEvalAction M .pos 0 none (some (satEvalQ q a c false))).apply _ = _
  exact satEvalAction_apply M saved u _ _ i (i + 1) (by omega) (by omega)
    j j .pos 0 (moveInputPos_pos_of_ne_right _ (by simp <;> omega)) (by simp)

/-- A local semantic transition followed by its skip consumes a doubled bit.
The last work head moves only on the first of the two physical transitions.

**Proof sketch.** Apply the semantic transition with the stated input and work-head move, then apply the
silent skip. The two native positions remain inside the doubled input. -/
private lemma satEval_double (M : FinTM Bool) {w : List Bool}
    (saved : Cfg M.k Bool M.State w) (u : List Bool)
    (q q' : Fin 5) (a c a' c' b : Bool) (i : ℕ) (hi : i + 2 ≤ w.length)
    (j j' : ℤ) (d : SignType) (hd : j + d.cast = j')
    (hin : w[i]? = some b)
    (htr : (satEvalTM M).tm.tr (.inr (satEvalQ q a c false)) (some b)
      (satEvalCfg M saved u (satEvalQ q a c false) i (by omega) j).workTapeSymbols =
        satEvalAction M .pos d none (some (satEvalQ q' a' c' true))) :
    (satEvalTM M).tm.runFrom
      (satEvalCfg M saved u (satEvalQ q a c false) i (by omega) j) 2 =
        satEvalCfg M saved u (satEvalQ q' a' c' false) (i + 2) hi j' := by
  have hs : (satEvalTM M).tm.step
      (satEvalCfg M saved u (satEvalQ q a c false) i (by omega) j) =
        satEvalCfg M saved u (satEvalQ q' a' c' true) (i + 1) (by omega) j' := by
    unfold MultiTapeTM.step
    change ((satEvalTM M).tm.tr (.inr (satEvalQ q a c false)) _ _).apply _ = _
    rw [satEvalCfg_input, hin, htr]
    exact satEvalAction_apply M saved u _ _ i (i + 1) (by omega) (by omega)
      j j' .pos d (moveInputPos_pos_of_ne_right _ (by simp <;> omega)) hd
  change (satEvalTM M).tm.step ((satEvalTM M).tm.step _) = _
  rw [hs, satEval_skip M saved u q' a' c' (i + 1) (by omega) j']

/-- Any left-moving certificate rewind takes exactly `n+1` steps from head
`n-1`, returns to zero, and preserves all native input and output fields.

**Proof sketch.** Induct on `n`. At `-1` the buffer is blank; otherwise its
cell is a certificate bit, so one silent left move exposes the shorter case. -/
private lemma satEval_rewind (M : FinTM Bool) {w : List Bool}
    (saved : Cfg M.k Bool M.State w) (u : List Bool) (q dest : SatEvalControl)
    (htr : ∀ inp work, (satEvalTM M).tm.tr (.inr q) inp work =
      match work (Fin.last M.k) with
      | some _ => satEvalAction M 0 .neg none (some q)
      | none => satEvalAction M 0 .pos none (some dest))
    (i : ℕ) (hi : i ≤ w.length) (n : ℕ) (hn : n ≤ u.length) :
    (satEvalTM M).tm.runFrom (satEvalCfg M saved u q i hi ((n : ℤ) - 1)) (n + 1) =
      satEvalCfg M saved u dest i hi 0 := by
  induction n with
  | zero =>
    simp only [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    unfold MultiTapeTM.step
    change ((satEvalTM M).tm.tr (.inr q) _ _).apply _ = _
    rw [htr, satEvalCfg_work]
    simp only [Int.natCast_zero, zero_sub, FinTM.bufferTape_left]
    exact satEvalAction_apply M saved u q dest i i hi hi (-1) 0 0 .pos
      (moveInputPos_zero _) (by simp)
  | succ n ih =>
    have hw : FinTM.bufferTape u (((n + 1 : ℕ) : ℤ) - 1) = some u[n] := by
      simp [FinTM.bufferTape, List.getElem?_eq_getElem (by omega : n < u.length)]
    have hs : (satEvalTM M).tm.step
        (satEvalCfg M saved u q i hi (((n + 1 : ℕ) : ℤ) - 1)) =
          satEvalCfg M saved u q i hi ((n : ℤ) - 1) := by
      unfold MultiTapeTM.step
      change ((satEvalTM M).tm.tr (.inr q) _ _).apply _ = _
      rw [htr, satEvalCfg_work, hw]
      exact satEvalAction_apply M saved u q q i i hi hi _ _ 0 .neg
        (moveInputPos_zero _) (by simp [SignType.cast] <;> omega)
    rw [MultiTapeTM.runFrom_succ_eq_step, hs, ih (by omega)]

/-- The native pairing prefix doubles every formula bit. -/
private def satBits (x : List Bool) : List Bool := x.flatMap fun b => [b, b]

/-- Doubled data has exactly twice the native length. -/
private lemma satBits_length (x : List Bool) : (satBits x).length = 2 * x.length := by
  induction x with
  | nil => rfl
  | cons b x ih => simp [satBits, List.flatMap_cons] at * <;> omega

/-- A unary index scan advances the certificate head once per remaining one.
The first one of a literal is consumed by the clause state, so this scan's
count is the variable index, not its successor. -/
private lemma satEval_index (M : FinTM Bool) {w : List Bool}
    (saved : Cfg M.k Bool M.State w) (u : List Bool) (a c : Bool)
    (n : ℕ) : ∀ pre rest (hw : w = pre ++ satBits (List.replicate n true) ++ rest) (j : ℤ),
    (satEvalTM M).tm.runFrom
      (satEvalCfg M saved u (satEvalQ 2 a c false) pre.length (by simp [hw]) j) (2 * n) =
        satEvalCfg M saved u (satEvalQ 2 a c false) (pre.length + 2 * n)
          (by simp only [hw, List.length_append, satBits_length, List.length_replicate] <;> omega)
          (j + n) := by
  induction n with
  | zero => intros; simp [MultiTapeTM.runFrom_zero]
  | succ n ih =>
    intro pre rest hw j
    have hw' : w = (pre ++ [true, true]) ++ satBits (List.replicate n true) ++ rest := by
      simpa [satBits, List.replicate_succ, List.append_assoc] using hw
    have hi : pre.length + 2 ≤ w.length := by simp [hw']
    have hs := satEval_double M saved u 2 2 a c a c true pre.length hi j (j + 1)
      .pos (by simp) (by simp [hw', List.append_assoc]) (by rfl)
    conv_lhs => rw [show 2 * (n + 1) = 2 + 2 * n by omega, MultiTapeTM.runFrom_add, hs]
    have hr := ih (pre ++ [true, true]) rest hw' (j + 1)
    simpa [Nat.mul_add, add_assoc, add_comm, add_left_comm] using hr

/-- A literal walk and its rewind take exactly `3v+8` transitions, return the
certificate head to zero, and update only the clause truth bit.

**Proof sketch.** Consume the first doubled one, walk the remaining `v`
ones, read the terminator and polarity, and rewind `v+1` occupied cells.
The certificate-length hypothesis guarantees the compared cell is present. -/
private lemma satEval_literal (M : FinTM Bool) {w : List Bool}
    (saved : Cfg M.k Bool M.State w) (u : List Bool) (a c b : Bool) (v : ℕ)
    (hv : v < u.length) (pre rest : List Bool)
    (hw : w = pre ++ satBits (CNF.serializeLit (v, b)) ++ rest) :
    (satEvalTM M).tm.runFrom
      (satEvalCfg M saved u (satEvalQ 1 a c false) pre.length (by simp [hw]) 0) (3 * v + 8) =
      satEvalCfg M saved u (satEvalQ 1 a (c || (satAssignment u v == b)) false)
        (pre.length + 2 * (v + 3))
        (by simp [hw, satBits_length, CNF.serializeLit] <;> omega) 0 := by
  let p₁ := pre ++ [true, true]
  let p₂ := p₁ ++ satBits (List.replicate v true)
  let p₃ := p₂ ++ [false, false]
  let p₄ := p₃ ++ [b, b]
  have hw₁ : w = p₁ ++ satBits (List.replicate v true) ++ [false, false, b, b] ++ rest := by
    simpa [p₁, satBits, CNF.serializeLit, List.replicate_succ, List.append_assoc] using hw
  have hw₂ : w = p₂ ++ [false, false, b, b] ++ rest := hw₁
  have hw₃ : w = p₃ ++ [b, b] ++ rest := by simpa [p₃, List.append_assoc] using hw₂
  have hw₄ : w = p₄ ++ rest := by simpa [p₄, List.append_assoc] using hw₃
  have h₁ := satEval_double M saved u 1 2 a c a c true pre.length
    (by simp [hw₁, p₁] <;> omega) 0 0 0 (by simp)
    (by simp [hw₁, p₁, List.append_assoc]) (by rfl)
  have h₂ := satEval_index M saved u a c v p₁ ([false, false, b, b] ++ rest)
    (by simpa [List.append_assoc] using hw₁) 0
  have h₃ := satEval_double M saved u 2 3 a c a c false p₂.length
    (by simp [hw₂]) (v : ℤ) v 0 (by simp)
    (by simp [hw₂, List.append_assoc]) (by rfl)
  have hread : FinTM.bufferTape u (v : ℤ) = some (satAssignment u v) := by
    simp only [FinTM.bufferTape_nat, satAssignment, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem hv, Option.getD_some]
  have h₄ := satEval_double M saved u 3 4 a c a (c || (satAssignment u v == b)) b p₃.length
    (by simp [hw₃]) (v : ℤ) v 0 (by simp) (by simp [hw₃, List.append_assoc]) (by
      simp only [satEvalTM, satEvalQ, Bool.false_eq_true, ↓reduceIte]
      rw [satEvalCfg_work, hread]
      cases h : satAssignment u v <;> cases b <;> rfl)
  have h₅ := satEval_rewind M saved u (satEvalQ 4 a (c || (satAssignment u v == b)) false)
    (satEvalQ 1 a (c || (satAssignment u v == b)) false) (by intros; rfl)
    p₄.length (by simp [hw₄]) (v + 1) (by omega)
  have hl₂ : p₂.length = pre.length + 2 + 2 * v := by simp [p₂, p₁, satBits_length] <;> omega
  have hl₃ : p₃.length = pre.length + 2 + 2 * v + 2 := by simp [p₃, hl₂]
  have hl₄ : p₄.length = pre.length + 2 + 2 * v + 2 + 2 := by simp [p₄, hl₃]
  have hh₂ : (satEvalTM M).tm.runFrom
      (satEvalCfg M saved u (satEvalQ 2 a c false) (pre.length + 2) (by simp [hw₁, p₁] <;> omega) 0)
        (2 * v) = satEvalCfg M saved u (satEvalQ 2 a c false) p₂.length (by simp [hw₂]) v := by
    simpa [p₁, hl₂] using h₂
  have hh₃ : (satEvalTM M).tm.runFrom
      (satEvalCfg M saved u (satEvalQ 2 a c false) p₂.length (by simp [hw₂]) v) 2 =
        satEvalCfg M saved u (satEvalQ 3 a c false) p₃.length (by simp [hw₃]) v := by
    simpa [p₃] using h₃
  have hh₄ : (satEvalTM M).tm.runFrom
      (satEvalCfg M saved u (satEvalQ 3 a c false) p₃.length (by simp [hw₃]) v) 2 =
        satEvalCfg M saved u (satEvalQ 4 a (c || (satAssignment u v == b)) false)
          p₄.length (by simp [hw₄]) v := by
    simpa [p₄] using h₄
  have hh₅ : (satEvalTM M).tm.runFrom
      (satEvalCfg M saved u (satEvalQ 4 a (c || (satAssignment u v == b)) false)
        p₄.length (by simp [hw₄]) v) (v + 2) =
        satEvalCfg M saved u (satEvalQ 1 a (c || (satAssignment u v == b)) false)
          p₄.length (by simp [hw₄]) 0 := by simpa using h₅
  conv_lhs => rw [show 3 * v + 8 = 2 + (2 * v + (2 + (2 + (v + 2)))) by omega,
    MultiTapeTM.runFrom_add, h₁, MultiTapeTM.runFrom_add, hh₂,
    MultiTapeTM.runFrom_add, hh₃, MultiTapeTM.runFrom_add, hh₄, hh₅]
  congr 1
  omega

/-- A clause pass returns to formula control with its accumulated truth bit.
No verdict is emitted by this pass, even for an empty or false clause.

**Proof sketch.** Induct on literals, composing the exact literal walk with
the tail pass. The closing zero takes two physical transitions. Sum the
literal bounds against three times their unary serialization lengths. -/
private lemma satEval_clause (M : FinTM Bool) {w : List Bool}
    (saved : Cfg M.k Bool M.State w) (u : List Bool) (C : CNF.Clause ℕ)
    (hvars : ∀ ℓ ∈ C, ℓ.1 < u.length) :
    ∀ pre rest (hw : w = pre ++ satBits (CNF.serializeClause C) ++ rest) (a c : Bool),
    ∃ t ≤ 3 * (CNF.serializeClause C).length,
      (satEvalTM M).tm.runFrom
        (satEvalCfg M saved u (satEvalQ 1 a c false) pre.length (by simp [hw]) 0) t =
      satEvalCfg M saved u
        (satEvalQ 0 (a && (c || CNF.Clause.eval (satAssignment u) C)) false false)
        (pre.length + 2 * (CNF.serializeClause C).length)
        (by simp only [hw, List.length_append, satBits_length] <;> omega) 0 := by
  induction C with
  | nil =>
    intro pre rest hw a c
    refine ⟨2, by simp [CNF.serializeClause], ?_⟩
    have h := satEval_double M saved u 1 0 a c (a && c) false false pre.length
      (by simp [hw, CNF.serializeClause, satBits]) 0 0 0 (by simp)
      (by simp [hw, CNF.serializeClause, satBits]) (by rfl)
    simpa [CNF.serializeClause, CNF.Clause.eval_nil] using h
  | cons ℓ C ih =>
    intro pre rest hw a c
    have hv := hvars ℓ List.mem_cons_self
    have htvars : ∀ d ∈ C, d.1 < u.length := fun d hd => hvars d (List.mem_cons_of_mem ℓ hd)
    let pre' := pre ++ satBits (CNF.serializeLit ℓ)
    have hw' : w = pre' ++ satBits (CNF.serializeClause C) ++ rest := by
      simpa [pre', satBits, CNF.serializeClause, List.append_assoc] using hw
    have hl : pre'.length = pre.length + 2 * (ℓ.1 + 3) := by
      simp [pre', satBits_length, CNF.serializeLit] <;> omega
    have hs := satEval_literal M saved u a c ℓ.2 ℓ.1 hv pre
      (satBits (CNF.serializeClause C) ++ rest)
      (by simpa [pre', List.append_assoc] using hw')
    obtain ⟨t, ht, hr⟩ := ih htvars pre' rest hw' a (c || (satAssignment u ℓ.1 == ℓ.2))
    have hlen : (CNF.serializeClause (ℓ :: C)).length =
        ℓ.1 + 3 + (CNF.serializeClause C).length := by
      simp [CNF.serializeClause, CNF.serializeLit] <;> omega
    refine ⟨3 * ℓ.1 + 8 + t, by omega, ?_⟩
    rw [MultiTapeTM.runFrom_add, hs]
    simpa only [hl, hlen, Nat.mul_add, Nat.add_assoc, CNF.Clause.eval_cons, Bool.or_assoc] using hr

/-- The streaming evaluation pass computes the conjunction of all clauses.

**Proof sketch.** Induct on clauses. Each clause starts with its marker and
runs the silent clause pass; conjunction is accumulated in finite control.
Only the final formula terminator emits. The native formula length pays for
all unary walks and rewinds, including empty formulas and empty clauses. -/
private lemma satEval_formula (M : FinTM Bool) {w : List Bool}
    (saved : Cfg M.k Bool M.State w) (u : List Bool) (φ : CNF ℕ)
    (hvars : ∀ C ∈ φ, ∀ ℓ ∈ C, ℓ.1 < u.length) :
    ∀ pre rest (hw : w = pre ++ satBits (CNF.serialize φ) ++ rest) (a : Bool),
    ∃ t ≤ 3 * (CNF.serialize φ).length,
      ((satEvalTM M).tm.runFrom
        (satEvalCfg M saved u (satEvalQ 0 a false false) pre.length (by simp [hw]) 0) t).state = none ∧
      ((satEvalTM M).tm.runFrom
        (satEvalCfg M saved u (satEvalQ 0 a false false) pre.length (by simp [hw]) 0) t).output =
          [a && φ.eval (satAssignment u)] := by
  induction φ with
  | nil =>
    intro pre rest hw a
    refine ⟨1, by simp [CNF.serialize], ?_⟩
    have hin : (satEvalCfg M saved u (satEvalQ 0 a false false)
        pre.length (by simp [hw]) 0).inputSymbol = some false := by
      rw [satEvalCfg_input]
      simp [hw, CNF.serialize, satBits]
    simp only [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero,
      MultiTapeTM.step, satEvalCfg, satEvalQ] at hin ⊢
    rw [hin]
    simp [satEvalTM, satEvalAction, satEvalQ, CNF.eval_nil]
  | cons C φ ih =>
    intro pre rest hw a
    have hcvars : ∀ ℓ ∈ C, ℓ.1 < u.length := hvars C List.mem_cons_self
    have htvars : ∀ D ∈ φ, ∀ ℓ ∈ D, ℓ.1 < u.length :=
      fun D hD => hvars D (List.mem_cons_of_mem C hD)
    let pre₁ := pre ++ [true, true]
    let pre₂ := pre₁ ++ satBits (CNF.serializeClause C)
    have hw₁ : w = pre₁ ++ satBits (CNF.serializeClause C) ++ satBits (CNF.serialize φ) ++ rest := by
      simpa [pre₁, satBits, CNF.serialize, List.append_assoc] using hw
    have hw₂ : w = pre₂ ++ satBits (CNF.serialize φ) ++ rest := hw₁
    have h₁ := satEval_double M saved u 0 1 a false a false true pre.length
      (by simp [hw₁, pre₁]) 0 0 0 (by simp)
      (by simp [hw₁, pre₁, List.append_assoc]) (by rfl)
    obtain ⟨s, hs, hc⟩ := satEval_clause M saved u C hcvars pre₁
      (satBits (CNF.serialize φ) ++ rest) (by simpa [List.append_assoc] using hw₁) a false
    have hp₁ : pre₁.length = pre.length + 2 := by simp [pre₁]
    have hp₂ : pre₂.length = pre.length + 2 + 2 * (CNF.serializeClause C).length := by
      change (pre₁ ++ satBits (CNF.serializeClause C)).length = _
      rw [List.length_append, hp₁, satBits_length]
    have hc' : (satEvalTM M).tm.runFrom
        (satEvalCfg M saved u (satEvalQ 1 a false false) (pre.length + 2)
          (by simp [hw₁, pre₁]) 0) s =
        satEvalCfg M saved u (satEvalQ 0 (a && CNF.Clause.eval (satAssignment u) C) false false)
          pre₂.length (by simp [hw₂]) 0 := by
      simpa only [hp₁, hp₂, Bool.false_or] using hc
    obtain ⟨t, ht, hr⟩ := ih htvars pre₂ rest hw₂ (a && CNF.Clause.eval (satAssignment u) C)
    have hlen : (CNF.serialize (C :: φ)).length =
        1 + (CNF.serializeClause C).length + (CNF.serialize φ).length := by
      simp [CNF.serialize, CNF.serializeClause] <;> omega
    refine ⟨2 + (s + t), by omega, ?_⟩
    rw [MultiTapeTM.runFrom_add, h₁, MultiTapeTM.runFrom_add, hc']
    simpa only [CNF.eval_cons, Bool.and_assoc] using hr

/-- Select the actual first halting transition, retaining its final emission. -/
private lemma sat_first_halt (M : FinTM Bool) (x y : List Bool) (T : ℕ)
    (h : M.ComputesInTime x y T) :
    ∃ t ≤ T, (∀ r < t, (M.tm.runFrom (M.tm.initCfg x) r).state ≠ none) ∧
      (M.tm.runFrom (M.tm.initCfg x) t).state = none ∧
      (M.tm.runFrom (M.tm.initCfg x) t).output = y := by
  classical
  have hh := (FinTM.computesInTime_iff _ _ _ _).mp h
  have hex : ∃ t, (M.tm.runFrom (M.tm.initCfg x) t).state = none := ⟨T, hh.1⟩
  let t := Nat.find hex
  have ht : t ≤ T := Nat.find_min' hex hh.1
  have hs : (M.tm.runFrom (M.tm.initCfg x) t).state = none := Nat.find_spec hex
  have he := M.tm.runFrom_add (M.tm.initCfg x) t (T - t)
  rw [Nat.add_sub_of_le ht, MultiTapeTM.runFrom_of_halt _ hs] at he
  exact ⟨t, ht, fun r hr => Nat.find_min hex hr, hs, by rw [← he]; exact hh.2⟩

/-- Capture and both rewinds establish the evaluator's empty-output seam.

**Proof sketch.** Capture through the extractor's first halt (including a
halting emission), rewind the native input using the audited contract, then
rewind the immutable certificate buffer. Only the final evaluator emits. -/
private lemma satEval_start (M : FinTM Bool) (w u : List Bool) (T : ℕ)
    (hM : M.ComputesInTime w u T) :
    ∃ (saved : Cfg M.k Bool M.State w) (s : ℕ), s ≤ T + w.length + u.length + 5 ∧
      (satEvalTM M).tm.runFrom ((satEvalTM M).tm.initCfg w) s =
        satEvalCfg M saved u (satEvalQ 0 true false false) 0 (Nat.zero_le _) 0 := by
  obtain ⟨t, ht, hlive, hhalt, hout⟩ := sat_first_halt M w u T hM
  let saved := M.tm.runFrom (M.tm.initCfg w) t
  let captured := captureCfg (Sum.inl : M.State → (satEvalTM M).State)
    (.inr (.inl 0)) [] [] saved
  have hinit : (satEvalTM M).tm.initCfg w =
      captureCfg (Sum.inl : M.State → (satEvalTM M).State)
        (.inr (.inl 0)) [] [] (M.tm.initCfg w) := by
    refine Cfg.ext rfl rfl ?_ ?_ rfl
    · funext i z
      simp [captureCfg, MultiTapeTM.initCfg, Cfg.init, FinTM.bufferTape]
    · funext i
      simp [captureCfg, MultiTapeTM.initCfg, Cfg.init]
  have hcap : (satEvalTM M).tm.runFrom ((satEvalTM M).tm.initCfg w) t = captured := by
    rw [hinit]
    exact capture_run M.tm (satEvalTM M).tm Sum.inl (.inr (.inl 0))
      (by intros; rfl) [] [] (M.tm.initCfg w) t hlive
  have hstate : captured.state = some (.inr (.inl 0)) := by
    simp only [captured, captureCfg, saved, hhalt, Option.map_none, Option.getD_none]
  obtain ⟨r, hr, hrew⟩ := FinTM.timed_rewind (satEvalTM M).tm (.inr (.inl 0))
    (.inr (.inl 1)) (some (.inr (.inl 2))) (by intros; rfl) (by intros; rfl)
    captured hstate
  have hafter : {captured with state := some (.inr (.inl 2)), inputPos := 1} =
      satEvalCfg M saved u (.inl 2) 0 (Nat.zero_le _) u.length := by
    simp only [captured, captureCfg, saved, hout, List.nil_append, satEvalCfg]
    exact Cfg.ext rfl (by apply Fin.ext; simp) rfl rfl rfl
  rw [hafter] at hrew
  have hleft : (satEvalTM M).tm.step
      (satEvalCfg M saved u (.inl 2) 0 (Nat.zero_le _) u.length) =
        satEvalCfg M saved u (.inl 3) 0 (Nat.zero_le _) ((u.length : ℤ) - 1) := by
    unfold MultiTapeTM.step
    change (satEvalAction M 0 .neg none (some (.inl 3))).apply _ = _
    exact satEvalAction_apply M saved u _ _ 0 0 (Nat.zero_le _) (Nat.zero_le _)
      _ _ 0 .neg (moveInputPos_zero _) (by simp [SignType.cast]; omega)
  have htape := satEval_rewind M saved u (.inl 3) (satEvalQ 0 true false false)
    (by intros; rfl) 0 (Nat.zero_le _) u.length (Nat.le_refl _)
  refine ⟨saved, t + r + (u.length + 2), ?_, ?_⟩
  · have hp := captured.inputPos.isLt
    omega
  · have hprefix : (satEvalTM M).tm.runFrom ((satEvalTM M).tm.initCfg w) (t + r) =
        satEvalCfg M saved u (.inl 2) 0 (Nat.zero_le _) u.length := by
      rw [MultiTapeTM.runFrom_add, hcap, hrew]
    rw [MultiTapeTM.runFrom_add, hprefix, MultiTapeTM.runFrom_succ_eq_step, hleft, htape]

/-- One uniform finite evaluator works for every well-formed paired formula
and certificate covering its variables. Its full capture/startup/evaluation
cost is linear in the native paired-input length.

**Proof sketch.** Choose the catalog certificate extractor once. Capture its first halting run, establish
the evaluation seam, and run the formula pass. Its variable bound makes every assignment
lookup defined; combine the linear bounds. -/
private lemma satEval_computes : ∃ (E : FinTM Bool) (A : ℕ),
    ∀ (φ : CNF ℕ) (u : List Bool), (∀ C ∈ φ, ∀ ℓ ∈ C, ℓ.1 < u.length) →
      E.ComputesInTime (pairEncode (CNF.serialize φ) u) [φ.eval (satAssignment u)]
        (A * ((pairEncode (CNF.serialize φ) u).length + 1)) := by
  obtain ⟨M, B, hM⟩ := FinTM.computesFunInTime_pairSnd
  refine ⟨satEvalTM M, B + 6, ?_⟩
  intro φ u hv
  let w := pairEncode (CNF.serialize φ) u
  have hsource : M.ComputesInTime w u (B * (w.length + 1)) := by
    simpa only [w, pairDecode_pairEncode, Option.map_some, Option.getD_some] using hM w
  obtain ⟨saved, s, hs, hstart⟩ := satEval_start M w u (B * (w.length + 1)) hsource
  have hw : w = [] ++ satBits (CNF.serialize φ) ++ ([false, true] ++ u) := by
    simp [w, pairEncode, satBits, List.append_assoc]
  obtain ⟨t, ht, hhalt, hout⟩ := satEval_formula M saved u φ hv [] ([false, true] ++ u) hw true
  have hbase : (satEvalTM M).ComputesInTime w [φ.eval (satAssignment u)] (s + t) := by
    apply (FinTM.computesInTime_iff _ _ _ _).mpr
    rw [MultiTapeTM.runFrom_add, hstart]
    exact ⟨hhalt, by simpa only [Bool.true_and] using hout⟩
  apply hbase.mono
  have hwlen : w.length = 2 * (CNF.serialize φ).length + 2 + u.length := by
    change (satBits (CNF.serialize φ) ++ [false, true] ++ u).length = _
    simp [satBits_length] <;> omega
  change s + t ≤ (B + 6) * (w.length + 1)
  simp only [Nat.add_mul]
  omega

/-- Compose a computed request with a machine proved only on that request image.
The budget is measured at the original input length, as in the audited TMSAT construction. -/
private lemma sat_comp_on_image (M U : FinTM Bool) (f g : List Bool → List Bool)
    (T₁ T₂ : ℕ → ℕ) (hM : M.ComputesFunInTime f T₁)
    (hU : ∀ x, U.ComputesInTime (f x) (g x) (T₂ x.length)) :
    ∃ N : FinTM Bool, N.ComputesFunInTime g (fun n => 2 * T₁ n + T₂ n + 2) := by
  refine ⟨FinTM.bufferedCompTM M U, ?_⟩
  intro x
  obtain ⟨a, p, tapes, heads, ha, hstart⟩ :=
    FinTM.bufferedComp_start M U x (f x) (T₁ x.length) (hM x)
  have hlen : (f x).length ≤ T₁ x.length := by
    have ho := ((FinTM.computesInTime_iff _ _ _ _).mp (hM x)).2
    simpa only [ho] using M.tm.output_length_le x (T₁ x.length)
  obtain ⟨b, _, hr⟩ := FinTM.bufferedSecondCfg_run M U (U.tm.initCfg (f x)) true
    (by simp [FinTM.VirtualTag, MultiTapeTM.initCfg, Cfg.init]) p tapes heads (T₂ x.length)
  have hu := (FinTM.computesInTime_iff _ _ _ _).mp (hU x)
  have hbase : (FinTM.bufferedCompTM M U).ComputesInTime x (g x) (a + T₂ x.length) := by
    apply (FinTM.computesInTime_iff _ _ _ _).mpr
    rw [MultiTapeTM.runFrom_add, hstart, hr]
    exact ⟨by simpa only [FinTM.bufferedSecondCfg, Option.map_eq_none_iff] using hu.1, hu.2⟩
  exact hbase.mono (by dsimp only; omega)

/-- Linear-time catalog contracts are instances of the polynomial calculus. -/
private lemma sat_pt_linear (f : List Bool → List Bool)
    (h : ∃ (M : FinTM Bool) (C : ℕ),
      M.ComputesFunInTime f (fun n => C * (n + 1))) : PolyTimeComputable f := by
  obtain ⟨M, C, hM⟩ := h
  exact ⟨M, C, 1, by simpa only [Nat.pow_one] using hM⟩

/-- A fixed word is emitted from finite control. -/
private lemma sat_pt_const (w : List Bool) : PolyTimeComputable (fun _ => w) := by
  exact sat_pt_linear _ (FinTM.computesFunInTime_const w)

/-- Polynomial-time branches on the original input, using W3's captured
single-bit decision. All three budgets fit their maximum degree.

**Proof sketch.** Use the audited conditional constructor on the three witnessing machines. Bound each
monomial by the common maximum exponent and absorb the constructor overhead into one
coefficient. -/
private lemma sat_pt_cond {p : List Bool → Bool} {f g : List Bool → List Bool}
    (hp : PolyTimeComputable (fun x => [p x]))
    (hf : PolyTimeComputable f) (hg : PolyTimeComputable g) :
    PolyTimeComputable (fun x => if p x then f x else g x) := by
  obtain ⟨P, A, a, hP⟩ := hp
  obtain ⟨F, B, b, hF⟩ := hf
  obtain ⟨G, C, c, hG⟩ := hg
  obtain ⟨M, K, hM⟩ := FinTM.computesFunInTime_cond hP hF hG
  let e := max a (max b c)
  refine ⟨M, K * (A + B + C + 1), e, fun x => (hM x).mono ?_⟩
  have ha := Nat.mul_le_mul_left A
    (Nat.pow_le_pow_right (Nat.succ_pos x.length) (show a ≤ e by exact Nat.le_max_left _ _))
  have hb := Nat.mul_le_mul_left B
    (Nat.pow_le_pow_right (Nat.succ_pos x.length) (show b ≤ e by omega))
  have hc := Nat.mul_le_mul_left C
    (Nat.pow_le_pow_right (Nat.succ_pos x.length) (show c ≤ e by omega))
  have h1 : 1 ≤ (x.length + 1) ^ e := Nat.one_le_pow _ _ (Nat.succ_pos _)
  simp only [Nat.succ_eq_add_one] at ha hb hc
  calc
    _ ≤ K * ((A + B + C + 1) * (x.length + 1) ^ e) :=
      Nat.mul_le_mul_left K (by simp only [Nat.add_mul, Nat.one_mul]; omega)
    _ = _ := by ring


/-- Short-circuit conjunction preserves the order of two polynomial tests. -/
private lemma sat_pt_and {p q : List Bool → Bool}
    (hp : PolyTimeComputable (fun x => [p x]))
    (hq : PolyTimeComputable (fun x => [q x])) :
    PolyTimeComputable (fun x => [p x && q x]) := by
  have h := sat_pt_cond hp hq (sat_pt_const [false])
  convert h using 1
  funext x
  cases p x <;> rfl

/-- The catalog split emits an encoded pair, or an empty failure result. -/
private def satSplit (z : List Bool) : List Bool :=
  match solveSplit 1 1 z.length with
  | some i => pairEncode (z.take i) (z.drop i)
  | none => []

/-- Instance and certificate projections are guarded independently of their
empty-word defaults. -/
private def satInstance (z : List Bool) : List Bool :=
  ((pairDecode (satSplit z)).map Prod.fst).getD []

/-- The recovered certificate region. -/
private def satWitness (z : List Bool) : List Bool :=
  ((pairDecode (satSplit z)).map Prod.snd).getD []

/-- Exact split success; in particular this is false at every even length. -/
private def satSplitValid (z : List Bool) : Bool := (pairDecode (satSplit z)).isSome

/-- Full syntax validation runs only after successful split recovery. -/
private def satGood (z : List Bool) : Bool := satSplitValid z && satSyntax (satInstance z)

/-- Safe evaluator input: malformed formulas are replaced by the empty formula
before the evaluator runs. Thus no semantic rejection can precede validation. -/
private def satSafe (z : List Bool) : List Bool :=
  if satGood z then satSplit z else pairEncode (CNF.serialize []) []

/-- Evaluation result after the syntax pass; the fallback evaluates to true. -/
private def satSafeValue (z : List Bool) : Bool :=
  if satGood z then (CNF.decode (satInstance z)).eval (satAssignment (satWitness z)) else true

/-- Every actual literal lies below the existing formula variable bound.
This only exposes the defining maximum; finite-assignment evaluation uses the
already proved `eval_congr_of_lt_numVars`. -/
private lemma sat_literal_lt_numVars (φ : CNF ℕ) (C : CNF.Clause ℕ)
    (ℓ : Std.Sat.Literal ℕ) (hC : C ∈ φ) (hℓ : ℓ ∈ C) : ℓ.1 < φ.numVars := by
  apply Nat.lt_of_succ_le
  exact List.le_max_of_le
    (List.mem_flatMap.mpr ⟨C, hC, List.mem_map.mpr ⟨ℓ, hℓ, rfl⟩⟩) (Nat.le_refl _)

/-- Every safe request is a serialized formula with a covering certificate.
The conclusion holds also on failed splits and failed parses.

**Proof sketch.** A successful split gives an odd length and a witness longer than every decoded variable
index. Successful syntax reconstructs the serialization. In either failed-guard case,
the safe pair contains the empty formula, whose evaluation is true. -/
private lemma satSafe_spec (z : List Bool) :
    ∃ (φ : CNF ℕ) (u : List Bool), satSafe z = pairEncode (CNF.serialize φ) u ∧
      (∀ C ∈ φ, ∀ ℓ ∈ C, ℓ.1 < u.length) ∧
      φ.eval (satAssignment u) = satSafeValue z := by
  by_cases hg : satGood z = true
  · cases hs : solveSplit 1 1 z.length with
    | none => simp [satGood, satSplitValid, satSplit, hs, pairDecode] at hg
    | some i =>
      have hsyntax : (CNF.parse (z.take i)).isSome = true := by
        simpa [satGood, satSplitValid, satInstance, satSplit, hs,
          pairDecode_pairEncode, satSyntax_spec] using hg
      cases hp : CNF.parse (z.take i) with
      | none => simp [hp] at hsyntax
      | some φ =>
        have hdecode : CNF.decode (z.take i) = φ := by simp [CNF.decode, hp]
        have hi := sat_split_some z.length i hs
        have hlen : (z.drop i).length = (z.take i).length + 1 := by
          simp only [List.length_drop, List.length_take]; omega
        have hvars : φ.numVars ≤ (z.take i).length := by
          rw [← hdecode]; exact CNF.numVars_decode_le _
        refine ⟨φ, z.drop i, ?_, ?_, ?_⟩
        · simp only [satSafe, hg, ↓reduceIte, satSplit, hs, sat_parse_repr hp]
        · intro C hC ℓ hℓ
          have hv := sat_literal_lt_numVars φ C ℓ hC hℓ
          omega
        · simp [satSafeValue, hg, satInstance, satWitness, satSplit, hs,
            pairDecode_pairEncode, hdecode]
  · refine ⟨[], [], ?_, ?_, ?_⟩
    · simp [satSafe, hg]
    · simp
    · simp [satSafeValue, hg]

/-- Split recovery, projection, grammar validation, and safe request assembly
are all realized by the audited catalog and the complete syntax scanner. -/
private lemma sat_pipeline_poly :
    PolyTimeComputable (fun z => [satSplitValid z]) ∧
    PolyTimeComputable satInstance ∧
    PolyTimeComputable (fun z => [satSyntax (satInstance z)]) ∧
    PolyTimeComputable satSafe := by
  obtain ⟨M, A, hM⟩ := FinTM.computesFunInTime_splitSolve 1 1
  have hs : PolyTimeComputable satSplit := ⟨M, A, 3, hM⟩
  have hv : PolyTimeComputable (fun z => [satSplitValid z]) :=
    (sat_pt_linear _ FinTM.computesFunInTime_pairValid).comp hs
  have hx : PolyTimeComputable satInstance :=
    (sat_pt_linear _ FinTM.computesFunInTime_pairFst).comp hs
  have hp : PolyTimeComputable (fun z => [satSyntax (satInstance z)]) := satSyntax_poly.comp hx
  exact ⟨hv, hx, hp, sat_pt_cond (sat_pt_and hv hp) hs (sat_pt_const _)⟩

/-- The evaluator is polynomial on all safe requests.

**Proof sketch.** Use the evaluator only on the serialized inputs certified by
`satSafe_spec`. The request emitter's own output bound majorizes their lengths;
the original-input composition contract preserves the budget's argument. -/
private lemma satSafeValue_poly : PolyTimeComputable (fun z => [satSafeValue z]) := by
  obtain ⟨E, A, hE⟩ := satEval_computes
  obtain ⟨M, C, e, hM⟩ := sat_pipeline_poly.2.2.2
  have heval (z : List Bool) : E.ComputesInTime (satSafe z) [satSafeValue z]
      (A * (C * (z.length + 1) ^ e + 1)) := by
    obtain ⟨φ, u, hrequest, hvars, hvalue⟩ := satSafe_spec z
    have h := hE φ u hvars
    rw [← hrequest, hvalue] at h
    have hlen : (satSafe z).length ≤ C * (z.length + 1) ^ e := by
      have hout := ((FinTM.computesInTime_iff _ _ _ _).mp (hM z)).2
      simpa only [hout] using M.tm.output_length_le z (C * (z.length + 1) ^ e)
    exact h.mono (Nat.mul_le_mul_left A (by omega))
  obtain ⟨N, hN⟩ := sat_comp_on_image M E satSafe (fun z => [satSafeValue z])
    (fun n => C * (n + 1) ^ e) (fun n => A * (C * (n + 1) ^ e + 1)) hM heval
  refine ⟨N, 2 * C + A * (C + 1) + 2, e, fun z => (hN z).mono ?_⟩
  have hp : 1 ≤ (z.length + 1) ^ e := Nat.one_le_pow _ _ (Nat.succ_pos _)
  have ha : A ≤ A * (z.length + 1) ^ e := by
    simpa using Nat.mul_le_mul_left A hp
  dsimp only
  simp only [Nat.add_mul, Nat.mul_add, Nat.mul_one, Nat.mul_assoc]
  omega

/-- The SAT verifier rejects failed splits and otherwise uses the safe
evaluation pipeline. Failed parses take its accepting fallback branch. -/
private lemma satVerdict_false_poly : PolyTimeComputable (fun z => [satVerdict false z]) := by
  have h := sat_pt_cond sat_pipeline_poly.1 satSafeValue_poly (sat_pt_const [false])
  convert h using 1
  funext z
  cases hs : solveSplit 1 1 z.length with
  | none => simp [satVerdict, satSplitValid, satSplit, hs, pairDecode]
  | some i =>
    cases hp : CNF.parse (z.take i) <;>
      simp [satVerdict, satSplitValid, satSplit, hs, pairDecode_pairEncode,
        satSafeValue, satGood, satInstance, satWitness, satSyntax_spec, hp, CNF.decode, CNF.fallback]

/-- A computed singleton Boolean verdict decides its verifier language. -/
private lemma satVerifier_of_poly (three : Bool)
    (h : PolyTimeComputable (fun z => [satVerdict three z])) : satVerifier three ∈ P := by
  obtain ⟨M, C, e, hM⟩ := h
  apply mem_P_iff.mpr
  refine ⟨C, e, M, fun z => ?_⟩
  have ho : [satVerdict three z] =
      [MultiTapeTM.indicator (satVerifier three : Set (List Bool)) z] := by
    simp [satVerifier, MultiTapeTM.indicator]
  simpa only [ho] using hM z

/-- **`SAT ∈ NP`** [AB09, Theorem 2.10, membership]: the satisfying assignment
is the certificate.

**Proof sketch.** Certificate parameters `(C, c) = (1, 1)`: length exactly
`(n + 1)` bits. A certificate `u` encodes the assignment `a_u = fun v => u.getD v
false`; by `Std.Sat.CNF.numVars_decode_le` the decoded formula mentions only
variables `< n`, and `Complexity.eval_congr_of_lt_numVars` makes the first
`numVars` bits decisive — so `x` is satisfiable iff some length-`(n+1)`
certificate `u` makes `(CNF.decode x).eval a_u = true` (forward: truncate a
satisfying assignment to `n + 1` bits; backward: `a_u` itself). The verifier
language is `V = {x ++ u : |u| = |x| + 1 ∧ (CNF.decode x).eval a_u = true}`;
`V ∈ P` by a machine with the named fill obligations: (i) unique-split recovery
— on input `y` of length `m`, the split `n + (n + 1) = m` forces `m` odd and
`n = (m - 1) / 2`, **rejecting explicitly on even `m`** (the round-3 pattern of
`Complexity.mem_NP_iff_exists_length_le`); (ii) the **parsing machine** for the
LL(1) grammar of `Std.Sat.CNF.parse` (run-length counting over unary indices;
on parse failure continue with the fallback, i.e. accept — the empty formula
evaluates `true`); (iii) the **evaluation machine**: stream the clauses; for a
literal `(v, b)`, walk to position `v` of the certificate region (the unary
index makes the walk linear) and compare with `b`; a clause with no satisfied
literal rejects the formula, exhausting all clauses accepts; (iv) the verdict
`[true]`/`[false]` with buffered output (the standing isolation obligation).
Budget: polynomial in `m`; conclude with `Complexity.mem_P_of_dtime_le`, and
`SAT ∈ NP` with `(1, 1, V)`. -/
theorem SAT_mem_NP : SAT ∈ NP := by
  refine ⟨1, 1, satVerifier false, satVerifier_of_poly false satVerdict_false_poly, ?_⟩
  intro x
  simpa only [Nat.pow_one, Nat.one_mul] using sat_verifier_equiv x

/-- Width scanning stores a saturated counter in finite control. -/
private def satWidthCap (n : ℕ) : Fin 4 := ⟨min n 3, by omega⟩

/-- A separate width pass, run only after the complete syntax pass. The
fourth literal clears the flag; scanning continues without emitting. -/
private def satWidthStep (s : Fin 6 × Fin 4 × Bool) (b : Bool) : Fin 6 × Fin 4 × Bool :=
  let (q, c, good) := s
  match q.val with
  | 0 => (satSyntaxStep q b, 0, good)
  | 1 => if b then (2, satWidthCap (c.val + 1), good && decide (c.val < 3))
      else (0, 0, good)
  | _ => (satSyntaxStep q b, c, good)

/-- Unary index bits do not increment the literal counter. -/
private lemma satWidth_index (n : ℕ) (c : Fin 4) (good : Bool) :
    (List.replicate n true).foldl satWidthStep (2, c, good) = (2, c, good) := by
  induction n with
  | zero => rfl
  | succ n ih => simpa [List.replicate_succ, satWidthStep, satSyntaxStep] using ih

/-- A complete literal increments the width counter exactly once, independently
of its variable index and polarity. -/
private lemma satWidth_literal (ℓ : Std.Sat.Literal ℕ) (c : Fin 4) (good : Bool) :
    (CNF.serializeLit ℓ).foldl satWidthStep (1, c, good) =
      (1, satWidthCap (c.val + 1), good && decide (c.val < 3)) := by
  simp only [CNF.serializeLit, List.replicate_succ, List.cons_append, List.foldl_cons]
  change (List.replicate ℓ.1 true ++ [false, ℓ.2]).foldl satWidthStep
    (2, satWidthCap (c.val + 1), good && decide (c.val < 3)) = _
  rw [List.foldl_append, satWidth_index]
  rfl

/-- The separate width pass counts literal occurrences, including repetitions.

**Proof sketch.** Induct on literals. Saturation at three plus a persistent
overflow flag is equivalent to the exact inequality for the total width.
The clause terminator resets the counter without resetting the flag. -/
private lemma satWidth_clause (C : CNF.Clause ℕ) (c : Fin 4) (good : Bool) :
    (CNF.serializeClause C).foldl satWidthStep (1, c, good) =
      (0, 0, good && decide (c.val + C.length ≤ 3)) := by
  induction C generalizing c good with
  | nil =>
    have hc : c.val ≤ 3 := by omega
    simp [CNF.serializeClause, satWidthStep, hc]
  | cons ℓ C ih =>
    have hs : CNF.serializeClause (ℓ :: C) = CNF.serializeLit ℓ ++ CNF.serializeClause C := by
      simp [CNF.serializeClause, List.append_assoc]
    rw [hs, List.foldl_append, satWidth_literal, ih]
    have he : (decide (c.val < 3) && decide ((satWidthCap (c.val + 1)).val + C.length ≤ 3)) =
        decide (c.val + (ℓ :: C).length ≤ 3) := by
      apply Bool.eq_iff_iff.mpr
      simp only [Bool.and_eq_true, decide_eq_true_eq, satWidthCap, List.length_cons]
      have hc := c.isLt
      omega
    rw [Bool.and_assoc, he]

/-- Every clause is checked; the empty formula passes vacuously. -/
private lemma satWidth_formula (φ : CNF ℕ) (good : Bool) :
    (CNF.serialize φ).foldl satWidthStep (0, 0, good) = (4, 0, good && satWidth φ) := by
  induction φ generalizing good with
  | nil => simp [CNF.serialize, satWidthStep, satSyntaxStep, satWidth]
  | cons C φ ih =>
    have hs : CNF.serialize (C :: φ) = true :: (CNF.serializeClause C ++ CNF.serialize φ) := by
      simp [CNF.serialize, List.append_assoc]
    rw [hs, List.foldl_cons]
    change (CNF.serializeClause C ++ CNF.serialize φ).foldl satWidthStep (1, 0, good) = _
    rw [List.foldl_append, satWidth_clause, ih]
    simp [satWidth, Bool.and_assoc]

/-- The final flag of the independent width pass. -/
private def satWidthScan (x : List Bool) : Bool := (x.foldl satWidthStep (0, 0, true)).2.2

/-- On valid syntax the scan computes exactly the width predicate. -/
private lemma satWidthScan_serialize (φ : CNF ℕ) : satWidthScan (CNF.serialize φ) = satWidth φ := by
  simp [satWidthScan, satWidth_formula]

/-- The width pass is a real finite machine, with no work tapes and `n+1` time. -/
private lemma satWidthScan_poly : PolyTimeComputable (fun x => [satWidthScan x]) := by
  refine ⟨satScanTM satWidthStep (0, 0, true) (fun s => s.2.2), 1, 1, ?_⟩
  simpa only [Nat.pow_one, Nat.one_mul, satWidthScan] using
    satScan_computes satWidthStep (0, 0, true) (fun s => s.2.2)

/-- The 3SAT machine validates the entire syntax before running the width pass,
and runs the evaluation pass only after width success.

**Proof sketch.** Compose the split validity, complete syntax, width, and evaluation machines through
nested conditionals. Split failure rejects; syntax failure accepts the empty fallback;
only successfully parsed inputs reach the width scan. -/
private lemma satVerdict_true_poly : PolyTimeComputable (fun z => [satVerdict true z]) := by
  have hw : PolyTimeComputable (fun z => [satWidthScan (satInstance z)]) :=
    satWidthScan_poly.comp sat_pipeline_poly.2.1
  have hsem := sat_pt_and hw satSafeValue_poly
  have hparse := sat_pt_cond sat_pipeline_poly.2.2.1 hsem (sat_pt_const [true])
  have h := sat_pt_cond sat_pipeline_poly.1 hparse (sat_pt_const [false])
  convert h using 1
  funext z
  cases hs : solveSplit 1 1 z.length with
  | none => simp [satVerdict, satSplitValid, satSplit, hs, pairDecode]
  | some i =>
    cases hp : CNF.parse (z.take i) with
    | none =>
      simp [satVerdict, satSplitValid, satSplit, hs, pairDecode_pairEncode,
        satSafeValue, satGood, satInstance, satWitness, satSyntax_spec, hp,
        CNF.decode, CNF.fallback, satWidth]
    | some φ =>
      have hx := sat_parse_repr hp
      simp [satVerdict, satSplitValid, satSplit, hs, pairDecode_pairEncode,
        satSafeValue, satGood, satInstance, satWitness, satSyntax_spec, hx,
        CNF.parse_serialize, CNF.decode_serialize, satWidthScan_serialize]

/-- **`3SAT ∈ NP`** [AB09, Theorem 2.10, membership].

**Proof sketch.** The `Complexity.SAT_mem_NP` verifier with one more pass:
after parsing, additionally scan each clause counting literals to at most
three, rejecting a wider clause (so the verifier decides membership of the
decoded formula in the 3CNF fragment before evaluating). The fallback formula
has no clauses and passes the width check, keeping non-well-formed strings on
the member side, as `Complexity.SAT3` requires. Same parameters `(1, 1)`, same
budget shape. -/
theorem SAT3_mem_NP : SAT3 ∈ NP := by
  refine ⟨1, 1, satVerifier true, satVerifier_of_poly true satVerdict_true_poly, ?_⟩
  intro x
  simpa only [Nat.pow_one, Nat.one_mul] using sat3_verifier_equiv x

/-- Clause evaluation is unchanged when every occurring variable agrees. -/
private lemma satClause_congr (C : CNF.Clause ℕ) (a b : ℕ → Bool)
    (h : ∀ ℓ ∈ C, a ℓ.1 = b ℓ.1) : CNF.Clause.eval a C = CNF.Clause.eval b C := by
  apply CNF.Clause.eval_congr
  intro v hv
  rcases hv with hv | hv
  · exact h (v, false) hv
  · exact h (v, true) hv

/-- Split a nonempty clause into the audited chain, threading the first unused
variable. Each recursive call drops one original literal from the tail.
[AB09, §2.3.5, proof of Lemma 2.14] -/
private def satChain (head : Std.Sat.Literal ℕ) : CNF.Clause ℕ → ℕ → CNF ℕ × ℕ
  | b :: c :: d :: rest, n =>
      let next := satChain (n, false) (c :: d :: rest) (n + 1)
      ([head, b, (n, true)] :: next.1, next.2)
  | rest, n => ([head :: rest], n)

/-- Clause splitting preserves the empty clause, which must remain false. -/
private def satSplitClause (C : CNF.Clause ℕ) (n : ℕ) : CNF ℕ × ℕ :=
  match C with
  | [] => ([[]], n)
  | head :: rest => satChain head rest n

/-- The allocator never moves backwards. -/
private lemma satChain_cursor (head : Std.Sat.Literal ℕ) (rest : CNF.Clause ℕ) (n : ℕ) :
    n ≤ (satChain head rest n).2 := by
  induction rest generalizing head n with
  | nil => exact Nat.le_refl _
  | cons b rest ih =>
    cases rest with
    | nil => exact Nat.le_refl _
    | cons c rest =>
      cases rest with
      | nil => exact Nat.le_refl _
      | cons d rest => exact Nat.le_trans (Nat.le_succ n) (ih (n, false) (n + 1))

/-- Every emitted chain clause has at most three literals. -/
private lemma satChain_width (head : Std.Sat.Literal ℕ) (rest : CNF.Clause ℕ) (n : ℕ) :
    (satChain head rest n).1.WidthAtMost 3 := by
  induction rest generalizing head n with
  | nil => simp [satChain, CNF.WidthAtMost]
  | cons b rest ih =>
    cases rest with
    | nil => simp [satChain, CNF.WidthAtMost]
    | cons c rest =>
      cases rest with
      | nil => simp [satChain, CNF.WidthAtMost]
      | cons d rest =>
        have ht := ih (n, false) (n + 1)
        simpa only [satChain, CNF.WidthAtMost, List.mem_cons, List.length_cons,
          List.length_nil, forall_eq_or_imp, Nat.reduceAdd, Nat.le_refl, true_and] using ht

/-- Projecting a satisfying chain assignment satisfies the original clause.
No freshness hypothesis is needed in this direction.

**Proof sketch.** Induct on the splitting. If neither first literal is true,
the first link forces its fresh positive literal, so the recursively satisfied
tail must be satisfied by an original literal rather than the fresh negation. -/
private lemma satChain_sound (head : Std.Sat.Literal ℕ) (rest : CNF.Clause ℕ) (n : ℕ)
    (a : ℕ → Bool) (h : (satChain head rest n).1.eval a = true) :
    CNF.Clause.eval a (head :: rest) = true := by
  induction rest generalizing head n with
  | nil => simpa [satChain] using h
  | cons b rest ih =>
    cases rest with
    | nil => simpa [satChain] using h
    | cons c rest =>
      cases rest with
      | nil => simpa [satChain] using h
      | cons d rest =>
        have hh : CNF.Clause.eval a [head, b, (n, true)] = true ∧
            (satChain (n, false) (c :: d :: rest) (n + 1)).1.eval a = true := by
          simpa only [satChain, CNF.eval_cons, Bool.and_eq_true] using h
        have ht := ih (n, false) (n + 1) hh.2
        have hfirst := hh.1
        clear h hh ih
        cases hn : a n <;> simp_all [CNF.Clause.eval_cons, CNF.Clause.eval_nil] <;> aesop

/-- One splitting step extends the assignment at precisely the fresh index.
Its value is the truth of the remaining tail, as in the audited sketch.

**Proof sketch.** Update the fresh index to the tail clause truth value. All original literals have
smaller indices and keep their values. Case analysis on the tail value proves both
emitted clauses. -/
private lemma satChain_extend_step (head b : Std.Sat.Literal ℕ) (tail : CNF.Clause ℕ)
    (n : ℕ) (a : ℕ → Bool) (hvars : ∀ ℓ ∈ head :: b :: tail, ℓ.1 < n)
    (hsat : CNF.Clause.eval a (head :: b :: tail) = true) :
    ∃ a' : ℕ → Bool, (∀ v < n, a' v = a v) ∧
      CNF.Clause.eval a' [head, b, (n, true)] = true ∧
      CNF.Clause.eval a' ((n, false) :: tail) = true := by
  let a' := Function.update a n (CNF.Clause.eval a tail)
  have hfix : ∀ v < n, a' v = a v := by
    intro v hv
    exact Function.update_of_ne (by omega : v ≠ n) _ _
  have hhead := hfix head.1 (hvars head (by simp))
  have hb := hfix b.1 (hvars b (by simp))
  have hn : a' n = CNF.Clause.eval a tail := by simp [a']
  have htail : CNF.Clause.eval a' tail = CNF.Clause.eval a tail := by
    apply satClause_congr
    intro ℓ hℓ
    exact hfix ℓ.1 (hvars ℓ (by simp [hℓ]))
  refine ⟨a', hfix, ?_, ?_⟩
  · simpa [CNF.Clause.eval_cons, CNF.Clause.eval_nil, hhead, hb, hn] using hsat
  · simp only [CNF.Clause.eval_cons, hn, htail]
    cases CNF.Clause.eval a tail <;> rfl

/-- A satisfying original clause extends to a satisfying chain assignment,
with every previously allocated variable preserved.

**Proof sketch.** Set the next fresh variable to the tail's truth value. Apply
induction to the clause beginning with its negation, with the cursor increased
by one. That extension preserves the three variables in the emitted link. -/
private lemma satChain_complete (head : Std.Sat.Literal ℕ) (rest : CNF.Clause ℕ) (n : ℕ)
    (a : ℕ → Bool) (hvars : ∀ ℓ ∈ head :: rest, ℓ.1 < n)
    (hsat : CNF.Clause.eval a (head :: rest) = true) :
    ∃ a' : ℕ → Bool, (∀ v < n, a' v = a v) ∧ (satChain head rest n).1.eval a' = true := by
  induction rest generalizing head n a with
  | nil => exact ⟨a, fun _ _ => rfl, by simpa [satChain] using hsat⟩
  | cons b rest ih =>
    cases rest with
    | nil => exact ⟨a, fun _ _ => rfl, by simpa [satChain] using hsat⟩
    | cons c rest =>
      cases rest with
      | nil => exact ⟨a, fun _ _ => rfl, by simpa [satChain] using hsat⟩
      | cons d rest =>
        obtain ⟨a₁, hfix, hfirst, htail⟩ := satChain_extend_step head b (c :: d :: rest) n a hvars hsat
        have hnext : ∀ ℓ ∈ (n, false) :: c :: d :: rest, ℓ.1 < n + 1 := by
          intro ℓ hℓ
          rcases List.mem_cons.mp hℓ with rfl | hℓ
          · simp
          · have hv := hvars ℓ (List.mem_cons_of_mem head (List.mem_cons_of_mem b hℓ))
            omega
        obtain ⟨a₂, hfix₂, hsat₂⟩ := ih (n, false) (n + 1) a₁ hnext htail
        refine ⟨a₂, fun v hv => (hfix₂ v (by omega)).trans (hfix v hv), ?_⟩
        have heq : CNF.Clause.eval a₂ [head, b, (n, true)] =
            CNF.Clause.eval a₁ [head, b, (n, true)] := by
          apply satClause_congr
          intro ℓ hℓ
          apply hfix₂
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hℓ
          have hhead := hvars head (by simp)
          have hb := hvars b (by simp)
          rcases hℓ with rfl | rfl | rfl <;> (try dsimp only) <;> omega
        simp only [satChain, CNF.eval_cons, heq, hfirst, hsat₂, Bool.true_and]

/-- Every variable in the chain is below its returned fresh-variable cursor.

**Proof sketch.** Induct on the remaining literals. Each new link uses only two original indices and the
current fresh index; the recursive cursor is at least its starting value, so all are
below the returned cursor. -/
private lemma satChain_vars (head : Std.Sat.Literal ℕ) (rest : CNF.Clause ℕ) (n : ℕ)
    (hvars : ∀ ℓ ∈ head :: rest, ℓ.1 < n) :
    ∀ D ∈ (satChain head rest n).1, ∀ ℓ ∈ D, ℓ.1 < (satChain head rest n).2 := by
  induction rest generalizing head n with
  | nil => simpa only [satChain, List.mem_singleton, forall_eq] using hvars
  | cons b rest ih =>
    cases rest with
    | nil => simpa only [satChain, List.mem_singleton, forall_eq] using hvars
    | cons c rest =>
      cases rest with
      | nil => simpa only [satChain, List.mem_singleton, forall_eq] using hvars
      | cons d rest =>
        have hnext : ∀ ℓ ∈ (n, false) :: c :: d :: rest, ℓ.1 < n + 1 := by
          intro ℓ hℓ
          rcases List.mem_cons.mp hℓ with rfl | hℓ
          · simp
          · have hv := hvars ℓ (List.mem_cons_of_mem head (List.mem_cons_of_mem b hℓ)); omega
        have hr := ih (n, false) (n + 1) hnext
        have hn := satChain_cursor (n, false) (c :: d :: rest) (n + 1)
        intro D hD ℓ hℓ
        simp only [satChain, List.mem_cons] at hD
        rcases hD with rfl | hD
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hℓ
          have hhead := hvars head (by simp)
          have hb := hvars b (by simp)
          rcases hℓ with rfl | rfl | rfl <;> dsimp only [satChain] <;> omega
        · exact hr D hD ℓ hℓ

/-- The clause allocator is monotone, also on the empty clause. -/
private lemma satSplitClause_cursor (C : CNF.Clause ℕ) (n : ℕ) :
    n ≤ (satSplitClause C n).2 := by
  cases C with
  | nil => exact Nat.le_refl _
  | cons head rest => exact satChain_cursor head rest n

/-- Splitting a clause always produces 3CNF. -/
private lemma satSplitClause_width (C : CNF.Clause ℕ) (n : ℕ) :
    (satSplitClause C n).1.WidthAtMost 3 := by
  cases C with
  | nil => simp [satSplitClause, CNF.WidthAtMost]
  | cons head rest => exact satChain_width head rest n

/-- The returned cursor bounds all output variables of a split clause. -/
private lemma satSplitClause_vars (C : CNF.Clause ℕ) (n : ℕ)
    (hvars : ∀ ℓ ∈ C, ℓ.1 < n) :
    ∀ D ∈ (satSplitClause C n).1, ∀ ℓ ∈ D, ℓ.1 < (satSplitClause C n).2 := by
  cases C with
  | nil => simp [satSplitClause]
  | cons head rest => exact satChain_vars head rest n hvars

/-- Every satisfying output assignment satisfies the original clause. -/
private lemma satSplitClause_sound (C : CNF.Clause ℕ) (n : ℕ) (a : ℕ → Bool)
    (h : (satSplitClause C n).1.eval a = true) : CNF.Clause.eval a C = true := by
  cases C with
  | nil => simpa [satSplitClause] using h
  | cons head rest => exact satChain_sound head rest n a h

/-- Every satisfying clause assignment extends while preserving earlier indices. -/
private lemma satSplitClause_complete (C : CNF.Clause ℕ) (n : ℕ) (a : ℕ → Bool)
    (hvars : ∀ ℓ ∈ C, ℓ.1 < n) (hsat : CNF.Clause.eval a C = true) :
    ∃ a', (∀ v < n, a' v = a v) ∧ (satSplitClause C n).1.eval a' = true := by
  cases C with
  | nil => simp at hsat
  | cons head rest => exact satChain_complete head rest n a hvars hsat

/-- Transform clauses in order, threading one global fresh-variable cursor.
[AB09, §2.3.5, proof of Lemma 2.14] -/
private def satTransformFrom : CNF ℕ → ℕ → CNF ℕ × ℕ
  | [], n => ([], n)
  | C :: φ, n =>
      let first := satSplitClause C n
      let tail := satTransformFrom φ first.2
      (first.1 ++ tail.1, tail.2)

/-- A literal-wise bound gives the existing maximum-based variable bound. -/
private lemma sat_numVars_le (φ : CNF ℕ) (n : ℕ)
    (hvars : ∀ C ∈ φ, ∀ ℓ ∈ C, ℓ.1 < n) : φ.numVars ≤ n := by
  apply List.max_le_of_forall_le
  intro v hv
  obtain ⟨C, hC, hv⟩ := List.mem_flatMap.mp hv
  obtain ⟨ℓ, hℓ, rfl⟩ := List.mem_map.mp hv
  exact Nat.succ_le_of_lt (hvars C hC ℓ hℓ)

/-- The formula transform is always in the 3CNF fragment. -/
private lemma satTransformFrom_width (φ : CNF ℕ) (n : ℕ) :
    (satTransformFrom φ n).1.WidthAtMost 3 := by
  induction φ generalizing n with
  | nil => simp [satTransformFrom, CNF.WidthAtMost]
  | cons C φ ih =>
    intro D hD
    rcases List.mem_append.mp hD with hD | hD
    · exact satSplitClause_width C n D hD
    · exact ih (satSplitClause C n).2 D hD

/-- Soundness composes across all clause chains with the same assignment. -/
private lemma satTransformFrom_sound (φ : CNF ℕ) (n : ℕ) (a : ℕ → Bool)
    (h : (satTransformFrom φ n).1.eval a = true) : φ.eval a = true := by
  induction φ generalizing n with
  | nil => rfl
  | cons C φ ih =>
    have hh : (satSplitClause C n).1.eval a = true ∧
        (satTransformFrom φ (satSplitClause C n).2).1.eval a = true := by
      simpa only [satTransformFrom, CNF.eval_append, Bool.and_eq_true] using h
    exact Bool.and_eq_true_iff.mpr ⟨satSplitClause_sound C n a hh.1, ih _ hh.2⟩

/-- Completeness threads extensions through the globally fresh cursor.

**Proof sketch.** Extend over the first clause, then over the remaining
formula. The second extension preserves the first chain because all its
variables lie below its returned cursor. Both preservation steps use the
existing `eval_congr_of_lt_numVars` theorem. -/
private lemma satTransformFrom_complete (φ : CNF ℕ) (n : ℕ) (a : ℕ → Bool)
    (hvars : ∀ C ∈ φ, ∀ ℓ ∈ C, ℓ.1 < n) (hsat : φ.eval a = true) :
    ∃ a', (∀ v < n, a' v = a v) ∧ (satTransformFrom φ n).1.eval a' = true := by
  induction φ generalizing n a with
  | nil => exact ⟨a, fun _ _ => rfl, rfl⟩
  | cons C φ ih =>
    have hh := Bool.and_eq_true_iff.mp hsat
    have hcvars : ∀ ℓ ∈ C, ℓ.1 < n := hvars C List.mem_cons_self
    have htvars : ∀ D ∈ φ, ∀ ℓ ∈ D, ℓ.1 < n :=
      fun D hD => hvars D (List.mem_cons_of_mem C hD)
    obtain ⟨a₁, hfix, hfirst⟩ := satSplitClause_complete C n a hcvars hh.1
    have hn := satSplitClause_cursor C n
    have htail : CNF.eval a₁ φ = true := by
      rw [eval_congr_of_lt_numVars (a := a₁) (b := a)
        (fun v hv => hfix v (Nat.lt_of_lt_of_le hv (sat_numVars_le φ n htvars)))]
      exact hh.2
    obtain ⟨a₂, hfix₂, hrest⟩ := ih (satSplitClause C n).2 a₁
      (fun D hD ℓ hℓ => Nat.lt_of_lt_of_le (htvars D hD ℓ hℓ) hn) htail
    refine ⟨a₂, fun v hv => (hfix₂ v (Nat.lt_of_lt_of_le hv hn)).trans (hfix v hv), ?_⟩
    have hfirst₂ : (satSplitClause C n).1.eval a₂ = true := by
      rw [eval_congr_of_lt_numVars (a := a₂) (b := a₁)
        (fun v hv => hfix₂ v (Nat.lt_of_lt_of_le hv
          (sat_numVars_le _ _ (satSplitClause_vars C n hcvars))))]
      exact hfirst
    simp only [satTransformFrom, CNF.eval_append, hfirst₂, hrest, Bool.true_and]

/-- The clause transform starts allocating at precisely `numVars`, as required
by the audited reduction sketch. -/
private def satTransform (φ : CNF ℕ) : CNF ℕ := (satTransformFrom φ φ.numVars).1

/-- Equisatisfiability of the formula-level transform, in both directions.
[AB09, Lemma 2.14] -/
private lemma satTransform_equisat (φ : CNF ℕ) : (satTransform φ).Satisfiable ↔ φ.Satisfiable := by
  constructor
  · rintro ⟨a, ha⟩; exact ⟨a, satTransformFrom_sound φ φ.numVars a ha⟩
  · rintro ⟨a, ha⟩
    obtain ⟨a', _, h⟩ := satTransformFrom_complete φ φ.numVars a
      (fun C hC ℓ hℓ => sat_literal_lt_numVars φ C ℓ hC hℓ) ha
    exact ⟨a', h⟩

/-- The full string-level reduction, including the prescribed malformed-input
fallback. [AB09, Lemma 2.14] -/
private def satReduction (x : List Bool) : List Bool := CNF.serialize (satTransform (CNF.decode x))

/-- Reduction correctness is quantified over every string, without a
well-formedness hypothesis. The empty fallback is fixed by the transform. -/
private lemma satReduction_correct (x : List Bool) : x ∈ SAT ↔ satReduction x ∈ SAT3 := by
  change (CNF.decode x).Satisfiable ↔
    (CNF.decode (satReduction x)).WidthAtMost 3 ∧ (CNF.decode (satReduction x)).Satisfiable
  rw [satReduction, CNF.decode_serialize, satTransform_equisat]
  exact (and_iff_right (satTransformFrom_width (CNF.decode x) (CNF.decode x).numVars)).symm

/-- Failed parsing maps to the serialization of the unchanged empty formula. -/
private lemma satReduction_fallback (x : List Bool) (h : CNF.parse x = none) :
    satReduction x = CNF.serialize [] := by
  simp [satReduction, CNF.decode, h, CNF.fallback, satTransform, satTransformFrom]

/-- A chain uses at most one fresh variable and one output clause per input
tail literal; these coarse bounds include all unsplit cases. -/
private lemma satChain_sizes (head : Std.Sat.Literal ℕ) (rest : CNF.Clause ℕ) (n : ℕ) :
    (satChain head rest n).2 ≤ n + rest.length ∧
      (satChain head rest n).1.length ≤ rest.length + 1 := by
  induction rest generalizing head n with
  | nil => simp [satChain]
  | cons b rest ih =>
    cases rest with
    | nil => simp [satChain]
    | cons c rest =>
      cases rest with
      | nil => simp [satChain]
      | cons d rest =>
        have ht := ih (n, false) (n + 1)
        simp only [satChain, List.length_cons] at *
        omega

/-- Coarse clause allocation and output-count bounds, including the empty clause. -/
private lemma satSplitClause_sizes (C : CNF.Clause ℕ) (n : ℕ) :
    (satSplitClause C n).2 ≤ n + C.length ∧ (satSplitClause C n).1.length ≤ C.length + 1 := by
  cases C with
  | nil => simp [satSplitClause]
  | cons head rest =>
    have h := satChain_sizes head rest n
    change (satChain head rest n).2 ≤ n + (rest.length + 1) ∧
      (satChain head rest n).1.length ≤ rest.length + 1 + 1
    omega

/-- Number of literal occurrences plus number of clauses, used only for size
bookkeeping; the empty clause contributes one. -/
private def satMeasure (φ : CNF ℕ) : ℕ := (φ.map fun C => C.length + 1).sum

/-- Freshness and linear combinatorial growth for the complete transformation.

**Proof sketch.** Induct on clauses. Both allocators are monotone; their
individual bounds add. First-chain variables stay below the cursor passed to
the tail, while the induction hypothesis bounds all tail variables. -/
private lemma satTransformFrom_bounds (φ : CNF ℕ) (n : ℕ)
    (hvars : ∀ C ∈ φ, ∀ ℓ ∈ C, ℓ.1 < n) :
    n ≤ (satTransformFrom φ n).2 ∧
    (satTransformFrom φ n).2 ≤ n + satMeasure φ ∧
    (satTransformFrom φ n).1.length ≤ satMeasure φ ∧
    (∀ D ∈ (satTransformFrom φ n).1, ∀ ℓ ∈ D, ℓ.1 < (satTransformFrom φ n).2) := by
  induction φ generalizing n with
  | nil => simp [satTransformFrom, satMeasure]
  | cons C φ ih =>
    have hn := satSplitClause_cursor C n
    have hc := satSplitClause_sizes C n
    have ht := ih (satSplitClause C n).2
      (fun D hD ℓ hℓ => Nat.lt_of_lt_of_le
        (hvars D (List.mem_cons_of_mem C hD) ℓ hℓ) hn)
    have hv := satSplitClause_vars C n (hvars C List.mem_cons_self)
    change n ≤ (satTransformFrom φ (satSplitClause C n).2).2 ∧ _
    refine ⟨Nat.le_trans hn ht.1, ?_, ?_, ?_⟩
    · simp only [satTransformFrom, satMeasure, List.map_cons, List.sum_cons]
      dsimp only [satMeasure] at ht
      omega
    · simp only [satTransformFrom, List.length_append, satMeasure, List.map_cons, List.sum_cons]
      dsimp only [satMeasure] at ht
      omega
    · intro D hD ℓ hℓ
      rcases List.mem_append.mp hD with hD | hD
      · exact Nat.lt_of_lt_of_le (hv D hD ℓ hℓ) ht.1
      · exact ht.2.2.2 D hD ℓ hℓ

/-- Every clause's serialization has room for all its literal occurrences. -/
private lemma sat_clause_measure (C : CNF.Clause ℕ) : C.length + 1 ≤ (CNF.serializeClause C).length := by
  induction C with
  | nil => simp [CNF.serializeClause]
  | cons ℓ C ih => simp [CNF.serializeClause, CNF.serializeLit] at *; omega

/-- The combinatorial measure is bounded by the serialized input length. -/
private lemma sat_measure_serialize (φ : CNF ℕ) : satMeasure φ ≤ (CNF.serialize φ).length := by
  induction φ with
  | nil => simp [satMeasure, CNF.serialize]
  | cons C φ ih =>
    have hc := sat_clause_measure C
    have he : (CNF.serialize (C :: φ)).length =
        1 + (CNF.serializeClause C).length + (CNF.serialize φ).length := by
      simp [CNF.serialize, CNF.serializeClause]; omega
    simp only [satMeasure, List.map_cons, List.sum_cons] at *
    omega

/-- The bound applies to the total decoder as well as successful parses. -/
private lemma sat_measure_decode (x : List Bool) : satMeasure (CNF.decode x) ≤ x.length := by
  cases hp : CNF.parse x with
  | none => simp [CNF.decode, hp, CNF.fallback, satMeasure]
  | some φ =>
    have hx := sat_parse_repr hp
    simpa [CNF.decode, hp, hx, CNF.parse_serialize] using sat_measure_serialize φ

/-- Unary serialization of a variable-bounded clause has a linear size bound. -/
private lemma sat_clause_serial_bound (C : CNF.Clause ℕ) (n : ℕ)
    (hvars : ∀ ℓ ∈ C, ℓ.1 < n) :
    (CNF.serializeClause C).length ≤ C.length * (n + 2) + 1 := by
  induction C with
  | nil => simp [CNF.serializeClause]
  | cons ℓ C ih =>
    have hv := hvars ℓ List.mem_cons_self
    have ht := ih (fun d hd => hvars d (List.mem_cons_of_mem ℓ hd))
    have he : (CNF.serializeClause (ℓ :: C)).length =
        ℓ.1 + 3 + (CNF.serializeClause C).length := by
      simp [CNF.serializeClause, CNF.serializeLit]; omega
    rw [he, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

/-- Serialization of a variable-bounded 3CNF is linear in its clause count. -/
private lemma sat_serial_bound (φ : CNF ℕ) (n : ℕ) (hwidth : φ.WidthAtMost 3)
    (hvars : ∀ C ∈ φ, ∀ ℓ ∈ C, ℓ.1 < n) :
    (CNF.serialize φ).length ≤ φ.length * (3 * n + 8) + 1 := by
  induction φ with
  | nil => simp [CNF.serialize]
  | cons C φ ih =>
    have hc := sat_clause_serial_bound C n (hvars C List.mem_cons_self)
    have hm := Nat.mul_le_mul_right (n + 2) (hwidth C List.mem_cons_self)
    have ht := ih (fun D hD => hwidth D (List.mem_cons_of_mem C hD))
      (fun D hD => hvars D (List.mem_cons_of_mem C hD))
    have he : (CNF.serialize (C :: φ)).length =
        1 + (CNF.serializeClause C).length + (CNF.serialize φ).length := by
      simp [CNF.serialize, CNF.serializeClause]; omega
    rw [he, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

/-- The string reduction has quadratic output length on every input, including
malformed input of length zero. This is a size bound, not a machine-time claim. -/
private lemma satReduction_size (x : List Bool) :
    (satReduction x).length ≤ 6 * x.length ^ 2 + 8 * x.length + 1 := by
  let φ := CNF.decode x
  have h := satTransformFrom_bounds φ φ.numVars
    (fun C hC ℓ hℓ => sat_literal_lt_numVars φ C ℓ hC hℓ)
  have hn := CNF.numVars_decode_le x
  have hm := sat_measure_decode x
  have hcursor : (satTransformFrom φ φ.numVars).2 ≤ 2 * x.length := by
    change (satTransformFrom (CNF.decode x) (CNF.decode x).numVars).2 ≤ 2 * x.length
    dsimp only [φ] at h
    omega
  have hclauses : (satTransform φ).length ≤ x.length := Nat.le_trans h.2.2.1 hm
  have hs := sat_serial_bound (satTransform φ) (2 * x.length)
    (satTransformFrom_width φ φ.numVars)
    (fun D hD ℓ hℓ => Nat.lt_of_lt_of_le (h.2.2.2 D hD ℓ hℓ) hcursor)
  calc
    (satReduction x).length ≤ (satTransform φ).length * (3 * (2 * x.length) + 8) + 1 := hs
    _ ≤ x.length * (3 * (2 * x.length) + 8) + 1 :=
      Nat.add_le_add_right (Nat.mul_le_mul_right _ hclauses) 1
    _ = 6 * x.length ^ 2 + 8 * x.length + 1 := by ring

/-- Two-tape actions for the reduction: the first tape is a unary fresh
cursor, the second a temporary literal buffer. -/
private def satRedAction (m : SignType) (w₀ w₁ : Option (Option Bool))
    (d₀ d₁ : SignType) (out : Option Bool) (q : Option (Fin 35)) :
    Action 2 Bool (Fin 35) :=
  ⟨m, fun i => if i = 0 then (w₀, d₀) else (w₁, d₁), out, q⟩

/-- A candidate clause-splitting transducer on previously validated CNF words.
States 2--6 compute the maximum unary literal length silently. States 7--8
rewind the native input; states 9--34 are the proposed streaming serializer.
The buffer's permanent left marker is installed by states 0--1.

**Partial-delivery frontier.** `satRed_start` verifies initialization, the
maximum pass, and rewind. The streaming states still need their correctness
and time proofs; this definition is not a `PolyTimeComputable` witness. -/
private def satRedTM : FinTM Bool where
  k := 2
  State := Fin 35
  tm := {
    q₀ := 0
    tr := fun q inp work =>
      let a := satRedAction
      match q.val with
      | 0 => a 0 none none 0 .neg none (some 1)
      | 1 => a 0 none (some (some false)) 0 .pos none (some 2)
      | 2 => if inp = some true then a .pos none none 0 0 none (some 3)
        else a 0 none none 0 0 none (some 7)
      | 3 => if inp = some true then a .pos (some (some true)) none .pos 0 none (some 4)
        else a .pos none none 0 0 none (some 2)
      | 4 => if inp = some true then a .pos (some (some true)) none .pos 0 none (some 4)
        else a .pos none none .neg 0 none (some 6)
      | 5 => a .pos none none 0 0 none (some 3)
      | 6 => if (work 0).isSome then a 0 none none .neg 0 none (some 6)
        else a 0 none none .pos 0 none (some 5)
      | 7 => a .neg none none 0 0 none (some 8)
      | 8 => if inp.isSome then a .neg none none 0 0 none (some 8)
        else a .pos none none 0 0 none (some 9)
      | 9 => if inp = some true then a .pos none none 0 0 (some true) (some 10)
        else a 0 none none 0 0 (some false) none
      | 10 => if inp = some true then a .pos none none 0 0 (some true) (some 11)
        else a .pos none none 0 0 (some false) (some 9)
      | 11 => if inp = some true then a .pos none none 0 0 (some true) (some 11)
        else a .pos none none 0 0 (some false) (some 12)
      | 12 => a .pos none none 0 0 inp (some 13)
      | 13 => if inp = some true then a .pos none none 0 0 (some true) (some 14)
        else a .pos none none 0 0 (some false) (some 9)
      | 14 => if inp = some true then a .pos none none 0 0 (some true) (some 14)
        else a .pos none none 0 0 (some false) (some 15)
      | 15 => a .pos none none 0 0 inp (some 16)
      | 16 => if inp = some true then a .pos none (some (some true)) 0 .pos none (some 17)
        else a .pos none none 0 0 (some false) (some 9)
      | 17 => if inp = some true then a .pos none (some (some true)) 0 .pos none (some 17)
        else a .pos none (some (some false)) 0 .pos none (some 18)
      | 18 => a .pos none (some inp) 0 .neg none (some 19)
      | 19 => a 0 none none 0 .neg none (some 20)
      | 20 => if work 1 = some true then a 0 none none 0 .neg none (some 20)
        else a 0 none none 0 .pos none (some 21)
      | 21 => if inp = some true then a 0 none none 0 0 none (some 22)
        else a 0 none none 0 0 none (some 33)
      | 22 => if (work 0).isSome then a 0 none none .pos 0 (some true) (some 22)
        else a 0 none none 0 0 (some true) (some 23)
      | 23 => a 0 none none 0 0 (some false) (some 24)
      | 24 => a 0 none none 0 0 (some true) (some 25)
      | 25 => a 0 none none 0 0 (some false) (some 26)
      | 26 => a 0 none none 0 0 (some true) (some 27)
      | 27 => a 0 none none .neg 0 none (some 28)
      | 28 => if (work 0).isSome then a 0 none none .neg 0 none (some 28)
        else a 0 none none .pos 0 none (some 29)
      | 29 => if (work 0).isSome then a 0 none none .pos 0 (some true) (some 29)
        else a 0 (some (some true)) none 0 0 (some true) (some 30)
      | 30 => a 0 none none 0 0 (some false) (some 31)
      | 31 => a 0 none none .neg 0 (some false) (some 32)
      | 32 => if (work 0).isSome then a 0 none none .neg 0 none (some 32)
        else a 0 none none .pos 0 none (some 33)
      | 33 => match work 1 with
        | some b => a 0 none (some none) 0 .pos (some b) (some 33)
        | none => a 0 none none 0 .neg none (some 34)
      | _ => if (work 1).isSome then a 0 none none 0 .pos none (some 16)
        else a 0 none none 0 .neg none (some 34) }

/-- Canonical unary counter tape; its length is the next unused variable. -/
private def satRedCounter (n : ℕ) : ℤ → Option Bool := FinTM.bufferTape (List.replicate n true)

/-- Buffer cells before `cut` have been erased; the permanent marker at -1
allows return even after the payload has been completely erased. -/
private def satRedBuffer (word : List Bool) (cut : ℕ) (z : ℤ) : Option Bool :=
  if z = -1 then some false else if (cut : ℤ) ≤ z then FinTM.bufferTape word z else none

/-- A canonical frame exposes both tape heads and the accumulated output. -/
private def satRedCfg (x : List Bool) (q : Option (Fin 35)) (i : ℕ) (hi : i ≤ x.length)
    (n : ℕ) (buf : ℤ → Option Bool) (a b : ℤ) (out : List Bool) : Cfg 2 Bool (Fin 35) x :=
  ⟨q, ⟨i + 1, by omega⟩, (fun t => if t = 0 then satRedCounter n else buf),
    (fun t => if t = 0 then a else b), out⟩

/-- The canonical native input position reads the corresponding list cell. -/
private lemma satRedCfg_input (x : List Bool) (q : Option (Fin 35))
    (i : ℕ) (hi : i ≤ x.length) (n : ℕ) (buf : ℤ → Option Bool) (a b : ℤ) (out : List Bool) :
    (satRedCfg x q i hi n buf a b out).inputSymbol = x[i]? :=
  FinTM.inputSymbol_at _ i hi rfl

/-- The first tape's occupied cells are exactly its unary prefix. -/
private lemma satRedCounter_read (n j : ℕ) :
    satRedCounter n j = if j < n then some true else none := by
  simp [satRedCounter, FinTM.bufferTape_nat, List.getElem?_replicate]

/-- The counter's left boundary is blank. -/
private lemma satRedCounter_left (n : ℕ) : satRedCounter n (-1) = none := by
  simp [satRedCounter, FinTM.bufferTape_left]

/-- Writing within the current prefix preserves it; writing its right blank
extends the maximum by one. -/
private lemma satRedCounter_write (n j : ℕ) (hj : j ≤ n) :
    Function.update (satRedCounter n) (j : ℤ) (some true) = satRedCounter (max n (j + 1)) := by
  by_cases h : j < n
  · rw [max_eq_left (by omega)]
    exact Function.update_eq_self_iff.mpr (by simp [satRedCounter_read, h])
  · have he : j = n := by omega
    subst j
    simpa [satRedCounter, List.replicate_succ', max_eq_right (Nat.le_succ n)] using
      (FinTM.bufferTape_append (List.replicate n true) true).symm

/-- Frame-level action calculus keeps output append and both tape updates
explicit; it is shared by the maximum pass and the streaming serializer.

**Proof sketch.** Compare all five configuration fields. Split the two work-tape cases, substitute the
prescribed tape updates and integer head movements, and use the explicit output-append
equation. -/
private lemma satRedAction_apply (x : List Bool) (q q' : Option (Fin 35))
    (i i' : ℕ) (hi : i ≤ x.length) (hi' : i' ≤ x.length) (n n' : ℕ)
    (buf buf' : ℤ → Option Bool) (a b a' b' : ℤ) (out out' : List Bool)
    (m : SignType) (w₀ w₁ : Option (Option Bool)) (d₀ d₁ : SignType) (emit : Option Bool)
    (hm : moveInputPos (⟨i + 1, by omega⟩ : Fin (x.length + 2)) m = ⟨i' + 1, by omega⟩)
    (h₀ : (match w₀ with
      | none => satRedCounter n
      | some c => Function.update (satRedCounter n) a c) = satRedCounter n')
    (h₁ : (match w₁ with | none => buf | some c => Function.update buf b c) = buf')
    (ha : a + d₀.cast = a') (hb : b + d₁.cast = b')
    (ho : out ++ emit.toList = out') :
    (satRedAction m w₀ w₁ d₀ d₁ emit q').apply (satRedCfg x q i hi n buf a b out) =
      satRedCfg x q' i' hi' n' buf' a' b' out' := by
  refine Cfg.ext rfl hm ?_ ?_ ho
  · funext t
    fin_cases t
    · cases w₀ <;> simpa [satRedAction, satRedCfg, Action.apply] using h₀
    · cases w₁ <;> simpa [satRedAction, satRedCfg, Action.apply] using h₁
  · funext t
    fin_cases t
    · simpa [satRedAction, satRedCfg, Action.apply] using ha
    · simpa [satRedAction, satRedCfg, Action.apply] using hb

/-- A silent transition with no writes changes only control and head positions. -/
private lemma satRed_move (x : List Bool) (q q' : Fin 35)
    (i i' : ℕ) (hi : i ≤ x.length) (hi' : i' ≤ x.length) (n : ℕ)
    (buf : ℤ → Option Bool) (a b a' b' : ℤ) (out : List Bool)
    (m d₀ d₁ : SignType)
    (hm : moveInputPos (⟨i + 1, by omega⟩ : Fin (x.length + 2)) m = ⟨i' + 1, by omega⟩)
    (ha : a + d₀.cast = a') (hb : b + d₁.cast = b')
    (ht : satRedTM.tm.tr q (x[i]?) (fun t : Fin 2 => if t = 0 then satRedCounter n a else buf b) =
      satRedAction m none none d₀ d₁ none (some q')) :
    satRedTM.tm.step (satRedCfg x (some q) i hi n buf a b out) =
      satRedCfg x (some q') i' hi' n buf a' b' out := by
  unfold MultiTapeTM.step
  change (satRedTM.tm.tr q _ _).apply _ = _
  rw [satRedCfg_input]
  have hw : (satRedCfg x (some q) i hi n buf a b out).workTapeSymbols =
      (fun t => if t = 0 then satRedCounter n a else buf b) := by
    funext t
    fin_cases t <;> rfl
  rw [hw, ht]
  exact satRedAction_apply x (some q) (some q') i i' hi hi' n n buf buf a b a' b' out out
    m none none d₀ d₁ none hm rfl rfl ha hb (by simp)

/-- A single machine transition is the one-step run. -/
private lemma satRed_one {x : List Bool} (cfg : Cfg 2 Bool (Fin 35) x) :
    satRedTM.tm.runFrom cfg 1 = satRedTM.tm.step cfg := by
  rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]

/-- Counter rewinds take exactly `r+1` silent transitions, including the
left blank, and apply to each of the three return phases.

**Proof sketch.** Induct on the distance to the left boundary. An occupied counter cell gives one silent
left move; at the blank cell -1, the final right move enters the return state at head
zero. -/
private lemma satRed_counterBack (x : List Bool) (q dest : Fin 35)
    (htr : ∀ (inp : Option Bool) (work : Fin 2 → Option Bool), satRedTM.tm.tr q inp work =
      if (work 0).isSome then satRedAction 0 none none .neg 0 none (some q)
      else satRedAction 0 none none .pos 0 none (some dest))
    (i : ℕ) (hi : i ≤ x.length) (n r : ℕ) (hr : r ≤ n)
    (buf : ℤ → Option Bool) (b : ℤ) (out : List Bool) :
    satRedTM.tm.runFrom (satRedCfg x (some q) i hi n buf ((r : ℤ) - 1) b out) (r + 1) =
      satRedCfg x (some dest) i hi n buf 0 b out := by
  induction r with
  | zero =>
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    apply satRed_move x q dest i i hi hi n buf (-1) b 0 b out 0 .pos 0
      (moveInputPos_zero _) (by simp) (by simp)
    rw [htr]
    simp [satRedCounter_left]
  | succ r ih =>
    have hs : satRedTM.tm.step
        (satRedCfg x (some q) i hi n buf (((r + 1 : ℕ) : ℤ) - 1) b out) =
        satRedCfg x (some q) i hi n buf ((r : ℤ) - 1) b out := by
      apply satRed_move x q q i i hi hi n buf _ b _ b out 0 .neg 0
        (moveInputPos_zero _) (by simp <;> omega) (by simp)
      rw [htr]
      have he : (((r + 1 : ℕ) : ℤ) - 1) = r := by omega
      simp [he, satRedCounter_read, show r < n by omega]
    rw [MultiTapeTM.runFrom_succ_eq_step, hs, ih (by omega)]

/-- The maximum pass consumes a unary run, extending precisely to the
maximum of the old prefix and the visited position.

**Proof sketch.** Induct on the unary run. Writing the next occupied cell or right blank changes the
counter length to the corresponding maximum. Compose the one-step update with the
shorter run and reassociate the maxima. -/
private lemma satRed_maxOnes (x : List Bool) (v : ℕ) :
    ∀ pre rest (hx : x = pre ++ List.replicate v true ++ rest)
      (n j : ℕ) (hj : j ≤ n) (buf : ℤ → Option Bool) (b : ℤ) (out : List Bool),
    satRedTM.tm.runFrom
      (satRedCfg x (some 4) pre.length (by simp [hx]) n buf j b out) v =
      satRedCfg x (some 4) (pre.length + v) (by simp [hx])
        (max n (j + v)) buf (j + v) b out := by
  induction v with
  | zero => intros; simp [MultiTapeTM.runFrom_zero, max_eq_left, *]
  | succ v ih =>
    intro pre rest hx n j hj buf b out
    have hx' : x = (pre ++ [true]) ++ List.replicate v true ++ rest := by
      simpa [List.replicate_succ, List.append_assoc] using hx
    have hs : satRedTM.tm.step
        (satRedCfg x (some 4) pre.length (by simp [hx]) n buf j b out) =
        satRedCfg x (some 4) (pre.length + 1) (by simp [hx'])
          (max n (j + 1)) buf (j + 1) b out := by
      unfold MultiTapeTM.step
      change (satRedTM.tm.tr (4 : Fin 35) _ _).apply _ = _
      rw [satRedCfg_input, show x[pre.length]? = some true by simp [hx', List.append_assoc]]
      change (satRedAction .pos (some (some true)) none .pos 0 none (some 4)).apply _ = _
      exact satRedAction_apply x (some 4) (some 4) _ _ _ _ n (max n (j + 1))
        buf buf j b (j + 1) b out out .pos (some (some true)) none .pos 0 none
        (moveInputPos_pos_of_ne_right _ (by simp [hx'] <;> omega))
        (satRedCounter_write n j hj) rfl (by simp) (by simp) (by simp)
    rw [MultiTapeTM.runFrom_succ_eq_step, hs]
    have h := ih (pre ++ [true]) rest hx' (max n (j + 1)) (j + 1) (Nat.le_max_right _ _)
      buf b out
    have he : max (max n (j + 1)) (j + 1 + v) = max n (j + (v + 1)) := by omega
    simpa [he, Nat.add_assoc, add_assoc, add_comm, add_left_comm] using h

/-- One literal in the maximum pass takes `2v+5` transitions, records the
maximum of the prior bound and `v+1`, and restores the counter head.

**Proof sketch.** Consume the first unary bit, scan the remaining index bits, and consume the zero
separator. Rewind the counter before skipping polarity. The five phases cost one, v,
one, v+2, and one steps. -/
private lemma satRed_maxLiteral (x : List Bool) (v : ℕ) (pol : Bool)
    (pre rest : List Bool) (hx : x = pre ++ CNF.serializeLit (v, pol) ++ rest)
    (n : ℕ) (buf : ℤ → Option Bool) (b : ℤ) (out : List Bool) :
    satRedTM.tm.runFrom
      (satRedCfg x (some 3) pre.length (by simp [hx]) n buf 0 b out) (2 * v + 5) =
      satRedCfg x (some 3) (pre.length + (v + 3))
        (by simp [hx, CNF.serializeLit] <;> omega) (max n (v + 1)) buf 0 b out := by
  let p₁ := pre ++ [true]
  let p₂ := p₁ ++ List.replicate v true
  let p₃ := p₂ ++ [false]
  have hx₁ : x = p₁ ++ List.replicate v true ++ [false, pol] ++ rest := by
    simpa [p₁, CNF.serializeLit, List.replicate_succ, List.append_assoc] using hx
  have hx₂ : x = p₂ ++ [false, pol] ++ rest := hx₁
  have hx₃ : x = p₃ ++ [pol] ++ rest := by simpa [p₃, List.append_assoc] using hx₂
  have h₁ : satRedTM.tm.step
      (satRedCfg x (some 3) pre.length (by simp [hx]) n buf 0 b out) =
      satRedCfg x (some 4) p₁.length (by simp [hx₁]) (max n 1) buf 1 b out := by
    unfold MultiTapeTM.step
    change (satRedTM.tm.tr (3 : Fin 35) _ _).apply _ = _
    rw [satRedCfg_input, show x[pre.length]? = some true by simp [hx₁, p₁, List.append_assoc]]
    change (satRedAction .pos (some (some true)) none .pos 0 none (some 4)).apply _ = _
    exact satRedAction_apply x (some 3) (some 4) _ _ _ _ n (max n 1)
      buf buf 0 b 1 b out out .pos (some (some true)) none .pos 0 none
      (by
        simp only [p₁, List.length_append, List.length_singleton]
        exact moveInputPos_pos_of_ne_right _ (by simp [hx₁, p₁]))
      (satRedCounter_write n 0 (Nat.zero_le _)) rfl (by simp) (by simp) (by simp)
  have h₂ := satRed_maxOnes x v p₁ ([false, pol] ++ rest)
    (by simpa [List.append_assoc] using hx₁) (max n 1) 1 (Nat.le_max_right _ _) buf b out
  have he : max (max n 1) (1 + v) = max n (v + 1) := by omega
  have hh₂ : satRedTM.tm.runFrom
      (satRedCfg x (some 4) p₁.length (by simp [hx₁]) (max n 1) buf 1 b out) v =
      satRedCfg x (some 4) p₂.length (by simp [hx₂]) (max n (v + 1)) buf (v + 1) b out := by
    simpa [p₂, he, Nat.add_comm, Int.add_comm] using h₂
  have h₃ : satRedTM.tm.step
      (satRedCfg x (some 4) p₂.length (by simp [hx₂]) (max n (v + 1)) buf (v + 1) b out) =
      satRedCfg x (some 6) p₃.length (by simp [hx₃]) (max n (v + 1)) buf v b out := by
    apply satRed_move x 4 6 _ _ _ _ _ buf _ b _ b out .pos .neg 0
      (by
        simp only [p₃, List.length_append, List.length_singleton]
        exact moveInputPos_pos_of_ne_right _ (by simp [hx₂]))
      (by simp <;> omega) (by simp)
    simp [satRedTM, show x[p₂.length]? = some false by simp [hx₂, List.append_assoc]]
  have h₄ := satRed_counterBack x 6 5 (by intros; rfl) p₃.length (by simp [hx₃])
    (max n (v + 1)) (v + 1) (Nat.le_max_right _ _) buf b out
  have hh₄ : satRedTM.tm.runFrom
      (satRedCfg x (some 6) p₃.length (by simp [hx₃]) (max n (v + 1)) buf v b out) (v + 2) =
      satRedCfg x (some 5) p₃.length (by simp [hx₃]) (max n (v + 1)) buf 0 b out := by
    simpa using h₄
  have h₅ : satRedTM.tm.step
      (satRedCfg x (some 5) p₃.length (by simp [hx₃]) (max n (v + 1)) buf 0 b out) =
      satRedCfg x (some 3) (pre.length + (v + 3)) (by simp [hx, CNF.serializeLit] <;> omega)
        (max n (v + 1)) buf 0 b out := by
    apply satRed_move x 5 3 _ _ _ _ _ buf _ b _ b out .pos 0 0
      (by
        have hp : p₃.length = pre.length + v + 2 := by simp [p₃, p₂, p₁] <;> omega
        have hm := moveInputPos_pos_of_ne_right
          (⟨p₃.length + 1, by simp [hx₃] <;> omega⟩ : Fin (x.length + 2)) (by simp [hx₃])
        simpa only [hp, Nat.add_assoc] using hm)
      (by simp) (by simp)
    rfl
  rw [← satRed_one] at h₁
  rw [← satRed_one] at h₃
  rw [← satRed_one] at h₅
  conv_lhs => rw [show 2 * v + 5 = 1 + (v + (1 + ((v + 2) + 1))) by omega,
    MultiTapeTM.runFrom_add, h₁, MultiTapeTM.runFrom_add, hh₂,
    MultiTapeTM.runFrom_add, h₃, MultiTapeTM.runFrom_add, hh₄, h₅]

/-- Maximum folding distributes over list concatenation. -/
private lemma sat_foldMax_append (a b : List ℕ) :
    (a ++ b).foldr max 0 = max (a.foldr max 0) (b.foldr max 0) := by
  induction a with
  | nil => simp
  | cons v a ih => simp [ih, max_assoc]

/-- Clause maximum used by the scanner invariant. -/
private def satClauseVars (C : CNF.Clause ℕ) : ℕ := (C.map fun ℓ => ℓ.1 + 1).foldr max 0

/-- The scanner's clause accumulator agrees with the frozen variable bound. -/
private lemma sat_numVars_cons (C : CNF.Clause ℕ) (φ : CNF ℕ) :
    CNF.numVars (C :: φ) = max (satClauseVars C) φ.numVars := by
  simp only [CNF.numVars, List.flatMap_cons, sat_foldMax_append, satClauseVars]

/-- A complete clause maximum pass is silent, linear in its serialization,
and returns both work heads to their entry positions.

**Proof sketch.** Induct on literals, composing the literal maximum pass and the shorter clause pass. A
zero terminator returns to formula control. Each literal cost is bounded by twice its
serialized length. -/
private lemma satRed_maxClause (x : List Bool) (C : CNF.Clause ℕ) :
    ∀ pre rest (hx : x = pre ++ CNF.serializeClause C ++ rest)
      (n : ℕ) (buf : ℤ → Option Bool) (b : ℤ) (out : List Bool),
    ∃ t ≤ 2 * (CNF.serializeClause C).length,
      satRedTM.tm.runFrom
        (satRedCfg x (some 3) pre.length (by simp [hx]) n buf 0 b out) t =
      satRedCfg x (some 2) (pre.length + (CNF.serializeClause C).length)
        (by simp [hx]) (max n (satClauseVars C)) buf 0 b out := by
  induction C with
  | nil =>
    intro pre rest hx n buf b out
    refine ⟨1, by simp [CNF.serializeClause], ?_⟩
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    simp only [CNF.serializeClause, List.flatMap_nil, List.nil_append, List.length_singleton,
      satClauseVars, List.map_nil, List.foldr_nil, Nat.max_zero]
    apply satRed_move x 3 2 _ _ _ _ _ buf _ b _ b out .pos 0 0
      (moveInputPos_pos_of_ne_right _ (by simp [hx, CNF.serializeClause]))
      (by simp) (by simp)
    simp [satRedTM, show x[pre.length]? = some false by simp [hx, CNF.serializeClause]]
  | cons ℓ C ih =>
    intro pre rest hx n buf b out
    let pre' := pre ++ CNF.serializeLit ℓ
    have hx' : x = pre' ++ CNF.serializeClause C ++ rest := by
      simpa [pre', CNF.serializeClause, List.append_assoc] using hx
    have hp : pre'.length = pre.length + (ℓ.1 + 3) := by
      simp [pre', CNF.serializeLit] <;> omega
    have hs := satRed_maxLiteral x ℓ.1 ℓ.2 pre (CNF.serializeClause C ++ rest)
      (by simpa [pre', List.append_assoc] using hx') n buf b out
    obtain ⟨t, ht, hr⟩ := ih pre' rest hx' (max n (ℓ.1 + 1)) buf b out
    have hl : (CNF.serializeClause (ℓ :: C)).length =
        ℓ.1 + 3 + (CNF.serializeClause C).length := by
      simp [CNF.serializeClause, CNF.serializeLit] <;> omega
    refine ⟨2 * ℓ.1 + 5 + t, by omega, ?_⟩
    rw [MultiTapeTM.runFrom_add, hs]
    simpa only [hp, hl, satClauseVars, List.map_cons, List.foldr_cons,
      max_assoc, Nat.add_assoc] using hr

/-- The silent maximum pass over a whole formula reaches the rewind seam
with exactly `numVars` (or the larger incoming bound) on the first tape.

**Proof sketch.** Induct on clauses. Consume the clause marker, run the clause maximum pass, and recurse
on the remaining formula. Maximum folding identifies the accumulated tape length with
the frozen variable bound. -/
private lemma satRed_maxFormula (x : List Bool) (φ : CNF ℕ) :
    ∀ pre rest (hx : x = pre ++ CNF.serialize φ ++ rest)
      (n : ℕ) (buf : ℤ → Option Bool) (b : ℤ) (out : List Bool),
    ∃ t ≤ 2 * (CNF.serialize φ).length,
      satRedTM.tm.runFrom
        (satRedCfg x (some 2) pre.length (by simp [hx]) n buf 0 b out) t =
      satRedCfg x (some 7) (pre.length + (CNF.serialize φ).length - 1)
        (by simp only [hx, List.length_append] <;> omega) (max n φ.numVars) buf 0 b out := by
  induction φ with
  | nil =>
    intro pre rest hx n buf b out
    refine ⟨1, by simp [CNF.serialize], ?_⟩
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    simp only [CNF.serialize, List.flatMap_nil, List.nil_append, List.length_singleton,
      Nat.add_sub_cancel, CNF.numVars, List.foldr_nil, Nat.max_zero]
    apply satRed_move x 2 7 _ _ _ _ _ buf _ b _ b out 0 0 0
      (moveInputPos_zero _) (by simp) (by simp)
    simp [satRedTM, show x[pre.length]? = some false by simp [hx, CNF.serialize]]
  | cons C φ ih =>
    intro pre rest hx n buf b out
    let p₁ := pre ++ [true]
    let p₂ := p₁ ++ CNF.serializeClause C
    have hx₁ : x = p₁ ++ CNF.serializeClause C ++ CNF.serialize φ ++ rest := by
      simpa [p₁, CNF.serialize, List.append_assoc] using hx
    have hx₂ : x = p₂ ++ CNF.serialize φ ++ rest := hx₁
    have hs : satRedTM.tm.step
        (satRedCfg x (some 2) pre.length (by simp [hx]) n buf 0 b out) =
        satRedCfg x (some 3) p₁.length (by simp [hx₁]) n buf 0 b out := by
      apply satRed_move x 2 3 _ _ _ _ _ buf _ b _ b out .pos 0 0
        (by
          simp only [p₁, List.length_append, List.length_singleton]
          exact moveInputPos_pos_of_ne_right _ (by simp [hx₁, p₁]))
        (by simp) (by simp)
      simp [satRedTM, show x[pre.length]? = some true by simp [hx₁, p₁, List.append_assoc]]
    obtain ⟨s, hsbound, hsrun⟩ := satRed_maxClause x C p₁ (CNF.serialize φ ++ rest)
      (by simpa [List.append_assoc] using hx₁) n buf b out
    obtain ⟨t, ht, hr⟩ := ih p₂ rest hx₂ (max n (satClauseVars C)) buf b out
    have hp₂ : p₂.length = p₁.length + (CNF.serializeClause C).length := by simp [p₂]
    have hl : (CNF.serialize (C :: φ)).length =
        1 + (CNF.serializeClause C).length + (CNF.serialize φ).length := by
      simp [CNF.serialize, CNF.serializeClause] <;> omega
    refine ⟨1 + (s + t), by omega, ?_⟩
    rw [← satRed_one] at hs
    rw [MultiTapeTM.runFrom_add, hs, MultiTapeTM.runFrom_add, hsrun]
    have hn : max (max n (satClauseVars C)) (CNF.numVars φ) =
        max n (CNF.numVars (C :: φ)) := by rw [sat_numVars_cons, max_assoc]
    have hi : p₂.length + (CNF.serialize φ).length - 1 =
        pre.length + (CNF.serialize (C :: φ)).length - 1 := by
      simp only [p₂, p₁, List.length_append, List.length_singleton]
      omega
    have hi' : p₁.length + (CNF.serializeClause C).length + (CNF.serialize φ).length - 1 =
        pre.length + (CNF.serialize (C :: φ)).length - 1 := by simpa only [hp₂] using hi
    simpa only [hp₂, hi', hn] using hr

/-- The empty literal buffer has just its permanent left marker. -/
private lemma satRedBuffer_empty : satRedBuffer [] 0 =
    Function.update (fun _ : ℤ => (none : Option Bool)) (-1) (some false) := by
  funext z
  by_cases hz : z = -1
  · subst z; simp [satRedBuffer]
  · simp [satRedBuffer, hz, Function.update_of_ne hz, FinTM.bufferTape]

/-- Installing the buffer marker requires exactly two silent transitions.

**Proof sketch.** The first transition moves the buffer head to -1. The second writes the permanent false
marker and returns to zero, preserving the empty counter and empty output. -/
private lemma satRed_init (x : List Bool) :
    satRedTM.tm.runFrom (satRedTM.tm.initCfg x) 2 =
      satRedCfg x (some 2) 0 (Nat.zero_le _) 0 (satRedBuffer [] 0) 0 0 [] := by
  have hz : satRedCounter 0 = fun _ => none := by
    funext z; simp [satRedCounter, FinTM.bufferTape]
  have hinit : satRedTM.tm.initCfg x =
      satRedCfg x (some 0) 0 (Nat.zero_le _) 0 (fun _ => none) 0 0 [] := by
    apply Cfg.ext <;> simp [satRedTM, satRedCfg, hz]
  have h₁ : satRedTM.tm.step
      (satRedCfg x (some 0) 0 (Nat.zero_le _) 0 (fun _ => none) 0 0 []) =
      satRedCfg x (some 1) 0 (Nat.zero_le _) 0 (fun _ => none) 0 (-1) [] := by
    apply satRed_move x 0 1 0 0 _ _ 0 (fun _ => none) 0 0 0 (-1) [] 0 0 .neg
      (moveInputPos_zero _) (by simp) (by simp)
    rfl
  have h₂ : satRedTM.tm.step
      (satRedCfg x (some 1) 0 (Nat.zero_le _) 0 (fun _ => none) 0 (-1) []) =
      satRedCfg x (some 2) 0 (Nat.zero_le _) 0 (satRedBuffer [] 0) 0 0 [] := by
    unfold MultiTapeTM.step
    change (satRedAction 0 none (some (some false)) 0 .pos none (some 2)).apply _ = _
    exact satRedAction_apply x (some 1) (some 2) 0 0 _ _ 0 0 (fun _ => none)
      (satRedBuffer [] 0) 0 (-1) 0 0 [] [] 0 none (some (some false)) 0 .pos none
      (moveInputPos_zero _) rfl satRedBuffer_empty.symm (by simp) (by simp) (by simp)
  rw [hinit, MultiTapeTM.runFrom_succ_eq_step, h₁, satRed_one, h₂]

/-- The maximum pass and native rewind establish the streaming seam with
exactly `numVars` in unary, empty output, and both work heads at zero.

**Proof sketch.** Install the literal-buffer marker, run the complete silent
maximum scan, then use the audited native rewind contract. The bound is
linear in the serialized formula length and also covers the empty formula. -/
private lemma satRed_start (φ : CNF ℕ) :
    ∃ t ≤ 3 * (CNF.serialize φ).length + 5,
      satRedTM.tm.runFrom (satRedTM.tm.initCfg (CNF.serialize φ)) t =
      satRedCfg (CNF.serialize φ) (some 9) 0 (Nat.zero_le _) φ.numVars
        (satRedBuffer [] 0) 0 0 [] := by
  let x := CNF.serialize φ
  obtain ⟨s, hs, hr⟩ := satRed_maxFormula x φ [] [] (by simp [x])
    0 (satRedBuffer [] 0) 0 []
  have hr' : satRedTM.tm.runFrom
      (satRedCfg x (some 2) 0 (Nat.zero_le _) 0 (satRedBuffer [] 0) 0 0 []) s =
      satRedCfg x (some 7) (x.length - 1) (Nat.sub_le _ _) φ.numVars
        (satRedBuffer [] 0) 0 0 [] := by simpa [x] using hr
  let cfg := satRedCfg x (some 7) (x.length - 1) (Nat.sub_le _ _) φ.numVars
    (satRedBuffer [] 0) 0 0 []
  obtain ⟨r, hb, hrew⟩ := FinTM.timed_rewind satRedTM.tm (7 : Fin 35) (8 : Fin 35) (some (9 : Fin 35))
    (by
      intro inp work
      simp [satRedTM, satRedAction, FinTM.controlAction])
    (by
      intro inp work
      cases inp <;> simp [satRedTM, satRedAction, FinTM.controlAction]) cfg rfl
  have he : {cfg with state := some 9, inputPos := 1} =
      satRedCfg x (some 9) 0 (Nat.zero_le _) φ.numVars (satRedBuffer [] 0) 0 0 [] := by
    exact Cfg.ext rfl rfl rfl rfl rfl
  rw [he] at hrew
  refine ⟨2 + (s + r), by dsimp only [cfg, satRedCfg, x] at hb; omega, ?_⟩
  rw [MultiTapeTM.runFrom_add, satRed_init, MultiTapeTM.runFrom_add, hr']
  exact hrew

/-! **E3 continuation B: normalized streaming schedule.** The persistent state
contains only a fresh-variable cursor, the consumed input length, and one of
five grammar phases (formula, first literal, second literal, tail, finished).
The input head is reconstructed from the length on every round; no buffer or
marker is part of this state. The following word-level schedule is the one
fixed by emitter-infra round 2, finding 5. -/

/-- The three fields carried across a normalized emitter seam. -/
private structure SatStreamState where
  fresh : ℕ
  used : ℕ
  phase : Fin 5
  deriving DecidableEq

/-- A literal parser round trip, proved locally because the encoding module's
corresponding helper is private. -/
private lemma satStream_parseLit (l : Std.Sat.Literal ℕ) (r : List Bool) :
    CNF.parseLit (CNF.serializeLit l ++ r) = some (l, r) := by
  have ht (n : ℕ) : CNF.takeTrues (List.replicate n true ++ false :: l.2 :: r) =
      (n, false :: l.2 :: r) := by
    induction n with
    | zero => rfl
    | succ n ih => simpa [List.replicate_succ, CNF.takeTrues, ih]
  simp [CNF.serializeLit, List.append_assoc, CNF.parseLit, ht]

/-- One validated grammar round: consume a marker or a complete literal,
perform the tail lookahead, and return its output chunk and new state.
Finished states are absorbing. At an exhausted formula input the round emits the fallback terminator;
other local parse failures terminate silently. Complete validation selects
the fallback state before any round starts. -/
private def satStreamRound (x : List Bool) (s : SatStreamState) :
    SatStreamState × List Bool :=
  if s.phase = 4 then (s, []) else
  match x.drop s.used with
  | [] => (⟨s.fresh, s.used, 4⟩, [false])
  | false :: _ =>
      (⟨s.fresh, s.used + 1, if s.phase = 0 then 4 else 0⟩, [false])
  | true :: r =>
      if s.phase = 0 then (⟨s.fresh, s.used + 1, 1⟩, [true]) else
      match CNF.parseLit (true :: r) with
      | none => (⟨s.fresh, s.used, 4⟩, [])
      | some (l, rest) =>
          if s.phase = 3 ∧ rest.head? = some true then
            (⟨s.fresh + 1, s.used + (CNF.serializeLit l).length, 3⟩,
             CNF.serializeLit (s.fresh, true) ++ [false, true] ++
               CNF.serializeLit (s.fresh, false) ++ CNF.serializeLit l)
          else
            (⟨s.fresh, s.used + (CNF.serializeLit l).length,
                if s.phase = 1 then 2 else 3⟩, CNF.serializeLit l)

/-- Execute a prescribed number of normalized rounds, concatenating chunks
in their emission order. This is a pure schedule, not a time-computability claim. -/
private def satStreamRun (x : List Bool) : ℕ → SatStreamState → SatStreamState × List Bool
  | 0, s => (s, [])
  | k + 1, s =>
      let a := satStreamRound x s
      let b := satStreamRun x k a.1
      (b.1, a.2 ++ b.2)

/-- Splitting the round count composes endpoints and concatenates outputs.
**Proof sketch.** Induct on the first segment length; associativity of word
concatenation identifies the two ways of grouping the emitted chunks. -/
private lemma satStreamRun_add (x : List Bool) (m n : ℕ) (s : SatStreamState) :
    satStreamRun x (m + n) s =
      let a := satStreamRun x m s
      let b := satStreamRun x n a.1
      (b.1, a.2 ++ b.2) := by
  induction m generalizing s with
  | zero => simp [satStreamRun]
  | succ m ih =>
    rw [Nat.succ_add]
    simp only [satStreamRun, ih, List.append_assoc]

/-- Padding after the formula terminator contributes no further output. -/
private lemma satStreamRun_finished (x : List Bool) (k j p : ℕ) :
    satStreamRun x k ⟨j, p, 4⟩ = (⟨j, p, 4⟩, []) := by
  induction k with
  | zero => rfl
  | succ k ih => simp [satStreamRun, satStreamRound, ih]

/-- The output still pending after the first two literals, together with the
final fresh cursor. A tail link closes one clause and opens the next.
[AB09, §2.3.5, proof of Lemma 2.14] -/
private def satStreamTail : CNF.Clause ℕ → ℕ → List Bool × ℕ
  | [], j => ([false], j)
  | [l], j => (CNF.serializeLit l ++ [false], j)
  | l :: d :: rest, j =>
      let t := satStreamTail (d :: rest) (j + 1)
      (CNF.serializeLit (j, true) ++ [false, true] ++
        CNF.serializeLit (j, false) ++ CNF.serializeLit l ++ t.1, t.2)

/-- The initial clause marker is handled by the formula phase; this is the
rest of the clause's emitted serialization, including its final terminator. -/
private def satStreamClause (C : CNF.Clause ℕ) (j : ℕ) : List Bool × ℕ :=
  match C with
  | [] => ([false], j)
  | [a] => (CNF.serializeLit a ++ [false], j)
  | a :: b :: rest =>
      let t := satStreamTail rest j
      (CNF.serializeLit a ++ CNF.serializeLit b ++ t.1, t.2)

/-- The tail fragments are exactly the serialization of the banked chain
recurrence after its first two literals, with the same allocated cursor.
**Proof sketch.** If at most one tail literal remains, the original clause
has width at most three. Otherwise both recurrences allocate the same fresh
variable, emit the same link, and recurse on the same shorter tail. -/
private lemma satStreamTail_chain (a b : Std.Sat.Literal ℕ) (C : CNF.Clause ℕ) (j : ℕ) :
    (satChain a (b :: C) j).1.flatMap (fun D => true :: CNF.serializeClause D) =
      true :: (CNF.serializeLit a ++ CNF.serializeLit b ++ (satStreamTail C j).1) ∧
    (satChain a (b :: C) j).2 = (satStreamTail C j).2 := by
  induction C generalizing a b j with
  | nil => simp [satChain, satStreamTail, CNF.serializeClause, List.append_assoc]
  | cons c C ih =>
    cases C with
    | nil => simp [satChain, satStreamTail, CNF.serializeClause, List.append_assoc]
    | cons d C =>
      obtain ⟨ho, hj⟩ := ih (j, false) c (j + 1)
      simp only [CNF.serializeClause] at ho
      constructor
      · simp only [satChain, List.flatMap_cons, CNF.serializeClause, List.flatMap_cons,
          List.flatMap_nil, List.append_nil, ho, satStreamTail]
        simp only [List.append_assoc, List.cons_append, List.nil_append]
      · exact hj

/-- The clause-level schedule realizes `satSplitClause` exactly, including
the empty clause and all widths at most three. -/
private lemma satStreamClause_split (C : CNF.Clause ℕ) (j : ℕ) :
    (satSplitClause C j).1.flatMap (fun D => true :: CNF.serializeClause D) =
      true :: (satStreamClause C j).1 ∧
    (satSplitClause C j).2 = (satStreamClause C j).2 := by
  cases C with
  | nil => simp [satSplitClause, satStreamClause, CNF.serializeClause]
  | cons a C =>
    cases C with
    | nil => simp [satSplitClause, satChain, satStreamClause, CNF.serializeClause]
    | cons b C => exact satStreamTail_chain a b C j

/-- Re-finding the consumed prefix exposes a clause or formula terminator. -/
private lemma satStreamRound_false (x pre rest : List Bool) (j : ℕ) (q : Fin 5)
    (hq : q ≠ 4) (hx : x = pre ++ false :: rest) :
    satStreamRound x ⟨j, pre.length, q⟩ =
      (⟨j, pre.length + 1, if q = 0 then 4 else 0⟩, [false]) := by
  simp [satStreamRound, hq, hx]

/-- Re-finding the prefix exposes the next clause marker at formula level. -/
private lemma satStreamRound_marker (x pre rest : List Bool) (j : ℕ)
    (hx : x = pre ++ true :: rest) :
    satStreamRound x ⟨j, pre.length, 0⟩ = (⟨j, pre.length + 1, 1⟩, [true]) := by
  simp [satStreamRound, hx]

/-- A complete literal and its lookahead are read within one round, so the
literal buffer never occurs in a persistent seam. -/
private lemma satStreamRound_literal (x pre rest : List Bool) (j : ℕ) (q : Fin 5)
    (hq0 : q ≠ 0) (hq4 : q ≠ 4) (l : Std.Sat.Literal ℕ)
    (hx : x = pre ++ CNF.serializeLit l ++ rest) :
    satStreamRound x ⟨j, pre.length, q⟩ =
      if q = 3 ∧ rest.head? = some true then
        (⟨j + 1, pre.length + (CNF.serializeLit l).length, 3⟩,
         CNF.serializeLit (j, true) ++ [false, true] ++
           CNF.serializeLit (j, false) ++ CNF.serializeLit l)
      else
        (⟨j, pre.length + (CNF.serializeLit l).length, if q = 1 then 2 else 3⟩,
          CNF.serializeLit l) := by
  have hd : x.drop pre.length = CNF.serializeLit l ++ rest := by
    simp [hx, List.append_assoc]
  have hh : ∃ r, CNF.serializeLit l ++ rest = true :: r := by
    exact ⟨List.replicate l.1 true ++ [false, l.2] ++ rest,
      by simp [CNF.serializeLit, List.replicate_succ, List.append_assoc]⟩
  obtain ⟨r, hr⟩ := hh
  have hp := satStream_parseLit l rest
  rw [hr] at hp
  simp only [satStreamRound, hq4, ↓reduceIte, hd, hr, hq0, hp]

/-- Tail phase consumes exactly one round per remaining literal and one for
the clause terminator. Every tail link allocates precisely the banked cursor.
**Proof sketch.** Induct on the remaining literals. The empty case consumes
the terminator. The singleton case copies the last literal. With a nonempty
lookahead, the first round emits the fresh positive/negative link, and the
induction hypothesis handles the shorter tail at the incremented cursor. -/
private lemma satStreamRun_tail (C : CNF.Clause ℕ) (x : List Bool) :
    ∀ pre rest j, x = pre ++ CNF.serializeClause C ++ rest →
      satStreamRun x (C.length + 1) ⟨j, pre.length, 3⟩ =
        (⟨(satStreamTail C j).2, pre.length + (CNF.serializeClause C).length, 0⟩,
          (satStreamTail C j).1) := by
  induction C with
  | nil =>
    intro pre rest j hx
    have h := satStreamRound_false x pre rest j 3 (by decide) (by simpa [CNF.serializeClause] using hx)
    simpa [satStreamRun, CNF.serializeClause, satStreamTail] using h
  | cons l C ih =>
    intro pre rest j hx
    let pre' := pre ++ CNF.serializeLit l
    have hx' : x = pre' ++ CNF.serializeClause C ++ rest := by
      simpa [pre', CNF.serializeClause, List.append_assoc] using hx
    have hp : pre'.length = pre.length + (CNF.serializeLit l).length := by simp [pre']
    have hs := satStreamRound_literal x pre (CNF.serializeClause C ++ rest) j 3
      (by decide) (by decide) l (by simpa [CNF.serializeClause, List.append_assoc] using hx)
    cases C with
    | nil =>
      have ht := ih pre' rest j hx'
      simp only [List.length_nil, Nat.zero_add] at ht
      simp only [CNF.serializeClause, List.flatMap_nil, List.nil_append,
        List.singleton_append, List.head?_cons, Bool.false_eq_true, Option.some.injEq,
        and_false, ↓reduceIte, show (3 : Fin 5) ≠ 1 by decide] at hs
      simp only [List.length_cons, List.length_nil] at ht ⊢
      rw [satStreamRun, hs]
      simp only
      rw [← hp, ht]
      simp [satStreamTail, CNF.serializeClause, hp, List.append_assoc, Nat.add_assoc]
    | cons d C =>
      have ht := ih pre' rest (j + 1) hx'
      simp only [List.length_cons, Nat.add_assoc, Nat.reduceAdd] at ht
      have hh : (CNF.serializeClause (d :: C) ++ rest).head? = some true := by
        simp [CNF.serializeClause, CNF.serializeLit, List.replicate_succ, List.append_assoc]
      simp only [hh, and_self, ↓reduceIte] at hs
      simp only [List.length_cons] at ⊢
      rw [satStreamRun, hs]
      simp only
      rw [← hp, ht]
      simp [satStreamTail, CNF.serializeClause, hp, List.append_assoc, Nat.add_assoc]

/-- A whole clause body takes one round per literal and a final terminator
round, starting in first-literal control and returning to formula control.
**Proof sketch.** Handle zero and one literal directly. Otherwise the first
two rounds copy the first two literals, then invoke the tail induction. -/
private lemma satStreamRun_clause (C : CNF.Clause ℕ) (x pre rest : List Bool) (j : ℕ)
    (hx : x = pre ++ CNF.serializeClause C ++ rest) :
    satStreamRun x (C.length + 1) ⟨j, pre.length, 1⟩ =
      (⟨(satStreamClause C j).2, pre.length + (CNF.serializeClause C).length, 0⟩,
        (satStreamClause C j).1) := by
  cases C with
  | nil =>
    have h := satStreamRound_false x pre rest j 1 (by decide) (by simpa [CNF.serializeClause] using hx)
    simpa [satStreamRun, CNF.serializeClause, satStreamClause] using h
  | cons a C =>
    let pre₁ := pre ++ CNF.serializeLit a
    have h₁ := satStreamRound_literal x pre (CNF.serializeClause C ++ rest) j 1
      (by decide) (by decide) a (by simpa [CNF.serializeClause, List.append_assoc] using hx)
    simp only [show (1 : Fin 5) ≠ 3 by decide, false_and, ↓reduceIte] at h₁
    have hp₁ : pre₁.length = pre.length + (CNF.serializeLit a).length := by simp [pre₁]
    have hx₁ : x = pre₁ ++ CNF.serializeClause C ++ rest := by
      simpa [pre₁, CNF.serializeClause, List.append_assoc] using hx
    cases C with
    | nil =>
      have h₂ := satStreamRound_false x pre₁ rest j 2 (by decide)
        (by simpa [CNF.serializeClause] using hx₁)
      simp only [List.length_cons, List.length_nil]
      rw [satStreamRun, h₁]
      simp only
      rw [← hp₁, satStreamRun, h₂]
      simp [satStreamRun, satStreamClause, CNF.serializeClause, hp₁, List.append_assoc, Nat.add_assoc]
    | cons b C =>
      let pre₂ := pre₁ ++ CNF.serializeLit b
      have hp₂ : pre₂.length = pre₁.length + (CNF.serializeLit b).length := by simp [pre₂]
      have h₂ := satStreamRound_literal x pre₁ (CNF.serializeClause C ++ rest) j 2
        (by decide) (by decide) b (by simpa [CNF.serializeClause, List.append_assoc] using hx₁)
      simp only [show (2 : Fin 5) ≠ 3 by decide, false_and, ↓reduceIte,
        show (2 : Fin 5) ≠ 1 by decide] at h₂
      have ht := satStreamRun_tail C x pre₂ rest j
        (by simpa [pre₂, CNF.serializeClause, List.append_assoc] using hx₁)
      simp only [List.length_cons]
      rw [satStreamRun, h₁]
      simp only
      rw [← hp₁, satStreamRun, h₂]
      simp only
      rw [← hp₂, ht]
      simp [satStreamClause, CNF.serializeClause, hp₂, hp₁, List.append_assoc, Nat.add_assoc]

/-- The exact number of nonfinished rounds: two markers per clause, one
round per original literal, and one final formula terminator. -/
private def satStreamCount (φ : CNF ℕ) : ℕ :=
  (φ.map fun C => C.length + 2).sum + 1

/-- The complete validated schedule emits exactly the banked transform and
threads exactly its final fresh-variable cursor.
**Proof sketch.** Induct on clauses. Emit the opening marker, run the proved
clause schedule, then run the remaining formula at its updated cursor.
The formula terminator enters the absorbing finished phase. -/
private lemma satStreamRun_formula (φ : CNF ℕ) (x : List Bool) :
    ∀ pre rest j, x = pre ++ CNF.serialize φ ++ rest →
      satStreamRun x (satStreamCount φ) ⟨j, pre.length, 0⟩ =
        (⟨(satTransformFrom φ j).2, pre.length + (CNF.serialize φ).length, 4⟩,
          CNF.serialize (satTransformFrom φ j).1) := by
  induction φ with
  | nil =>
    intro pre rest j hx
    have h := satStreamRound_false x pre rest j 0 (by decide) (by simpa [CNF.serialize] using hx)
    simpa [satStreamRun, satStreamCount, CNF.serialize, satTransformFrom] using h
  | cons C φ ih =>
    intro pre rest j hx
    let pre₁ := pre ++ [true]
    let pre₂ := pre₁ ++ CNF.serializeClause C
    have hp₁ : pre₁.length = pre.length + 1 := by simp [pre₁]
    have hp₂ : pre₂.length = pre₁.length + (CNF.serializeClause C).length := by simp [pre₂]
    have hx₁ : x = pre₁ ++ CNF.serializeClause C ++ (CNF.serialize φ ++ rest) := by
      simpa [pre₁, CNF.serialize, List.append_assoc] using hx
    have hx₂ : x = pre₂ ++ CNF.serialize φ ++ rest := by
      simpa [pre₂, List.append_assoc] using hx₁
    have h₁ := satStreamRound_marker x pre (CNF.serializeClause C ++ CNF.serialize φ ++ rest) j
      (by simpa [pre₁, List.append_assoc] using hx₁)
    have h₂ := satStreamRun_clause C x pre₁ (CNF.serialize φ ++ rest) j hx₁
    have ht := ih pre₂ rest (satStreamClause C j).2 hx₂
    have hc : satStreamCount (C :: φ) = 1 + ((C.length + 1) + satStreamCount φ) := by
      simp [satStreamCount]; omega
    rw [hc, Nat.add_comm 1, satStreamRun, h₁]
    simp only
    rw [← hp₁, satStreamRun_add, h₂]
    simp only
    rw [← hp₂, ht]
    obtain ⟨ho, hj⟩ := satStreamClause_split C j
    simp only [satTransformFrom, hj]
    congr 1
    · congr 1
      simp [CNF.serialize, hp₂, hp₁, Nat.add_assoc] <;> omega
    · simp only [CNF.serialize, List.flatMap_append, ho, List.cons_append,
        List.nil_append, List.append_assoc]

/-- Every nonfinished round consumes at least one input bit; the concrete
count is bounded even for empty clauses and the empty formula. -/
private lemma satStreamCount_le (φ : CNF ℕ) :
    satStreamCount φ ≤ (CNF.serialize φ).length := by
  induction φ with
  | nil => simp [satStreamCount, CNF.serialize]
  | cons C φ ih =>
    have hc := sat_clause_measure C
    have hlen : (CNF.serialize (C :: φ)).length =
        1 + (CNF.serializeClause C).length + (CNF.serialize φ).length := by
      simp [CNF.serialize]; omega
    simp only [satStreamCount, List.map_cons, List.sum_cons] at ih ⊢
    omega

/-- `R(n)=n` supplies `n+1` rounds. After the exact semantic schedule finishes,
all remaining rounds are empty; hence the extra final round is harmless. -/
private lemma satStreamRun_serialize (φ : CNF ℕ) :
    (satStreamRun (CNF.serialize φ) ((CNF.serialize φ).length + 1)
      ⟨φ.numVars, 0, 0⟩).2 = CNF.serialize (satTransform φ) := by
  have h := satStreamRun_formula φ (CNF.serialize φ) [] [] φ.numVars (by simp)
  have hc := satStreamCount_le φ
  rw [show (CNF.serialize φ).length + 1 = satStreamCount φ +
      ((CNF.serialize φ).length + 1 - satStreamCount φ) by omega, satStreamRun_add]
  simp only [List.length_nil, Nat.zero_add, List.append_nil] at h
  rw [h]
  simp only
  rw [satStreamRun_finished]
  simp [satTransform]

/-- The scheduler's output is precisely the range-indexed concatenation
required by the emitting-loop contract. -/
private lemma satStreamRun_output (x : List Bool) (k : ℕ) (s : SatStreamState) :
    (satStreamRun x k s).2 = (List.range k).flatMap
      (fun i => (satStreamRound x ((fun s => (satStreamRound x s).1)^[i] s)).2) := by
  induction k generalizing s with
  | zero => rfl
  | succ k ih =>
    simp only [satStreamRun, ih, List.range_succ_eq_map, List.flatMap_cons,
      List.flatMap_map, Function.comp_apply, Function.iterate_zero_apply,
      Function.iterate_succ_apply]

/-- Pair-encoded seam word: unary fresh cursor, unary consumed length, and a
bounded unary phase tag. It contains no round-local literal buffer. -/
private def satStreamWord (s : SatStreamState) : List Bool :=
  pairEncode (List.replicate s.fresh true)
    (pairEncode (List.replicate s.used true) (List.replicate s.phase.val true))

/-- Total projections for private paired state words. Malformed words have
empty default components; invariants use only the encoded image. -/
private def satStreamFst (w : List Bool) : List Bool :=
  ((pairDecode w).map Prod.fst).getD []

/-- Second component of a private paired word, with the same empty default. -/
private def satStreamSnd (w : List Bool) : List Bool :=
  ((pairDecode w).map Prod.snd).getD []

/-- Decode the bounded control tag modulo five. The modulus only totalizes
malformed words and is the identity on all reachable tags. -/
private def satStreamRead (w : List Bool) : SatStreamState :=
  ⟨(satStreamFst w).length, (satStreamFst (satStreamSnd w)).length,
    ⟨(satStreamSnd (satStreamSnd w)).length % 5, Nat.mod_lt _ (by decide)⟩⟩

/-- The paired representation preserves all three fields exactly. -/
private lemma satStreamRead_word (s : SatStreamState) : satStreamRead (satStreamWord s) = s := by
  cases s with
  | mk j p q =>
    simp [satStreamRead, satStreamWord, satStreamFst, satStreamSnd,
      pairDecode_pairEncode, Nat.mod_eq_of_lt q.isLt]

/-- The state representation has linear size in its two unary counters. -/
private lemma satStreamWord_length (s : SatStreamState) :
    (satStreamWord s).length = 2 * s.fresh + 2 * s.used + s.phase.val + 4 := by
  simp only [satStreamWord, pairEncode, List.length_append, List.length_replicate]
  simp [List.length_flatMap, Nat.mul_add, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
    Nat.mul_comm] <;> omega

/-- A length-only invariant: offsets remain inside the native input, and at
most one fresh variable is allocated per consumed bit. -/
private def satStreamBound (x : List Bool) (s : SatStreamState) : Prop :=
  s.used ≤ x.length ∧ s.fresh ≤ x.length + s.used

/-- Every round preserves the invariant, including malformed local inputs.
**Proof sketch.** A marker consumes one bit without allocation. A successful
literal parse reconstructs the suffix, so its serialized length fits inside
the unread input; that length is at least three and pays for a possible
single allocation. Finished and local-failure cases preserve the counters. -/
private lemma satStreamRound_bound (x : List Bool) (s : SatStreamState)
    (hs : satStreamBound x s) : satStreamBound x (satStreamRound x s).1 := by
  rcases hs with ⟨hp, hj⟩
  unfold satStreamRound
  split
  · exact ⟨hp, hj⟩
  · cases hd : x.drop s.used with
    | nil => exact ⟨hp, hj⟩
    | cons b r =>
      have hl := congrArg List.length hd
      simp only [List.length_drop, List.length_cons] at hl
      cases b with
      | false => dsimp only [satStreamBound]; exact ⟨by omega, by omega⟩
      | true =>
        simp only
        split
        · dsimp only [satStreamBound]; exact ⟨by omega, by omega⟩
        · cases hparse : CNF.parseLit (true :: r) with
          | none => exact ⟨hp, hj⟩
          | some lr =>
            rcases lr with ⟨l, rest⟩
            have he := congrArg List.length (sat_parseLit_repr hparse)
            have hpos : 0 < (CNF.serializeLit l).length := by simp [CNF.serializeLit]
            simp only [List.length_cons, List.length_append] at he
            simp only
            split <;> dsimp only [satStreamBound] <;> exact ⟨by omega, by omega⟩

/-- Reachable cursors are at most twice the original input length, and the
whole state word has length at most `6n+8`. -/
private lemma satStreamBound_size (x : List Bool) (s : SatStreamState)
    (hs : satStreamBound x s) :
    s.fresh ≤ 2 * x.length ∧ (satStreamWord s).length ≤ 6 * x.length + 8 := by
  have hq := s.phase.isLt
  rw [satStreamWord_length]
  rcases hs with ⟨hp, hj⟩
  constructor <;> omega

/-- Every emitted chunk is bounded by the original input length, even when
one short token triggers two long fresh-index serializations. The largest
fragment is at most `5n+11`, as required by the audited round schedule.
**Proof sketch.** Successful parsing bounds the current literal by the unread
suffix; the invariant gives `j ≤ 2n`. The fragment has two fresh literals,
two clause-marker bits, and the copied literal. Other branches are shorter. -/
private lemma satStreamRound_chunk_bound (x : List Bool) (s : SatStreamState)
    (hs : satStreamBound x s) : (satStreamRound x s).2.length ≤ 5 * x.length + 11 := by
  have hj := (satStreamBound_size x s hs).1
  unfold satStreamRound
  split
  · simp
  · cases hd : x.drop s.used with
    | nil => simp
    | cons b r =>
      have hx := congrArg List.length hd
      simp only [List.length_drop, List.length_cons] at hx
      cases b with
      | false => simp
      | true =>
        simp only
        split
        · simp
        · cases hp : CNF.parseLit (true :: r) with
          | none => simp
          | some lr =>
            rcases lr with ⟨l, rest⟩
            have hl := congrArg List.length (sat_parseLit_repr hp)
            simp only [List.length_append, List.length_cons] at hl
            simp only
            split <;> simp [CNF.serializeLit] at * <;> omega

/-- Complete validation selects the startup state before emission. A failed
parse starts at the right boundary in formula control; its first round emits
only the fallback terminator and then becomes finished, even at input length zero. -/
private def satStreamStart (x : List Bool) : SatStreamState :=
  if satSyntax x then ⟨(CNF.decode x).numVars, 0, 0⟩ else ⟨0, x.length, 0⟩

/-- Both the valid and fallback startup states satisfy the loop invariant. -/
private lemma satStreamStart_bound (x : List Bool) : satStreamBound x (satStreamStart x) := by
  unfold satStreamStart
  split
  · exact ⟨Nat.zero_le _, by simpa using CNF.numVars_decode_le x⟩
  · exact ⟨Nat.le_refl _, Nat.zero_le _⟩

/-- Failed whole-string validation produces exactly `[false]`; no prefix of
the malformed string is emitted. This includes trailing-data failures. -/
private lemma satStreamRun_fallback (x : List Bool) (k : ℕ) :
    (satStreamRun x (k + 1) ⟨0, x.length, 0⟩).2 = [false] := by
  simp [satStreamRun, satStreamRound, satStreamRun_finished]

/-- Exact output identity on every string, before any machine-computability
claim: complete validation plus the normalized schedule is `satReduction`.
**Proof sketch.** A successful parser reconstructs the entire serialized
formula and invokes the formula induction. A failed parse selects the
right-boundary fallback state, whose only nonempty chunk is `[false]`. -/
private lemma satStreamRun_correct (x : List Bool) :
    (satStreamRun x (x.length + 1) (satStreamStart x)).2 = satReduction x := by
  cases hp : CNF.parse x with
  | none =>
    have hs : satSyntax x = false := by simp [satSyntax_spec, hp]
    rw [satStreamStart, hs]
    simpa [satReduction_fallback x hp] using satStreamRun_fallback x x.length
  | some φ =>
    have hx := sat_parse_repr hp
    have hd : CNF.decode x = φ := by simp [CNF.decode, hp]
    have hs : satSyntax x = true := by simp [satSyntax_spec, hp]
    simp only [satStreamStart, hs, ↓reduceIte, satReduction, hd]
    rw [hx]
    exact satStreamRun_serialize φ

/-- Encoded next-state function consumed by the audited emitter interface. -/
private def satStreamStep (x w : List Bool) : List Bool :=
  satStreamWord (satStreamRound x (satStreamRead w)).1

/-- Encoded chunk function consumed by the audited emitter interface. -/
private def satStreamEmit (x w : List Bool) : List Bool :=
  (satStreamRound x (satStreamRead w)).2

/-- The loop invariant includes canonical encoding and its original-input
length bound; arbitrary malformed state words are not admitted as seams. -/
private def satStreamInv (x w : List Bool) : Prop :=
  ∃ s, w = satStreamWord s ∧ satStreamBound x s

/-- The encoded invariant holds at startup. -/
private lemma satStreamInv_start (x : List Bool) :
    satStreamInv x (satStreamWord (satStreamStart x)) :=
  ⟨_, rfl, satStreamStart_bound x⟩

/-- The encoded invariant is closed under every loop step. -/
private lemma satStreamInv_step (x w : List Bool) (h : satStreamInv x w) :
    satStreamInv x (satStreamStep x w) := by
  rcases h with ⟨s, rfl, hs⟩
  refine ⟨(satStreamRound x s).1, ?_, satStreamRound_bound x s hs⟩
  simp [satStreamStep, satStreamRead_word]

/-- Encoded and structured iteration have the same orbit. -/
private lemma satStreamStep_iterate (x : List Bool) (s : SatStreamState) (k : ℕ) :
    (satStreamStep x)^[k] (satStreamWord s) =
      satStreamWord ((fun s => (satStreamRound x s).1)^[k] s) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, Function.iterate_succ_apply']
    simp [satStreamStep, satStreamRead_word]

/-- The exact expression returned by `exists_emitLoopTM`, with `R n = n`,
is the desired all-string reduction. This discharges the output-identity
obligation independently of the remaining native-machine realization. -/
private lemma satStream_output_identity (x : List Bool) :
    (List.range (x.length + 1)).flatMap (fun i =>
      satStreamEmit x ((satStreamStep x)^[i] (satStreamWord (satStreamStart x)))) =
        satReduction x := by
  simp only [satStreamStep_iterate, satStreamEmit, satStreamRead_word]
  rw [← satStreamRun_output]
  exact satStreamRun_correct x

/-- Administrative action for retaining a computed word beside its input.
The completed source bank is untouched; only the capture head may move. -/
private def satPairAction (M : FinTM Bool) (m d : SignType) (b : Option Bool)
    (q : Option (Fin 8)) : Action (M.k + 1) Bool (M.State ⊕ Fin 8) :=
  ⟨m, fun i => (none, if i.val < M.k then 0 else d), b, q.map Sum.inr⟩

/-- Capture `f x`, rewind both heads, replay its bits twice, emit the pairing
separator, then copy native `x`. Thus the output is `pairEncode (f x) x`.
This private data-retaining combinator supplies the two-field round arguments. -/
private def satPairTM (M : FinTM Bool) : FinTM Bool where
  k := M.k + 1
  State := M.State ⊕ Fin 8
  tm := {
    q₀ := .inl M.tm.q₀
    tr := fun q inp work => match q with
    | .inl q => captureAction Sum.inl (.inr 0)
        (M.tm.tr q inp (fun i => work (Fin.castSucc i)))
    | .inr q => match q.val with
      | 0 => FinTM.controlAction .neg (some (.inr 1))
      | 1 => if inp.isSome then FinTM.controlAction .neg (some (.inr 1))
        else FinTM.controlAction .pos (some (.inr 2))
      | 2 => satPairAction M 0 .neg none (some 3)
      | 3 => if (work (Fin.last M.k)).isSome then satPairAction M 0 .neg none (some 3)
        else satPairAction M 0 .pos none (some 4)
      | 4 => match work (Fin.last M.k) with
        | some b => satPairAction M 0 0 (some b) (some 5)
        | none => satPairAction M 0 0 (some false) (some 6)
      | 5 => satPairAction M 0 .pos (work (Fin.last M.k)) (some 4)
      | 6 => satPairAction M 0 0 (some true) (some 7)
      | _ => match inp with
        | some b => satPairAction M .pos 0 (some b) (some 7)
        | none => satPairAction M 0 0 none none }

/-- Saved source scratch and its immutable captured word during pairing. -/
private def satPairCfg (M : FinTM Bool) {x : List Bool}
    (saved : Cfg M.k Bool M.State x) (u : List Bool) (q : Option (Fin 8))
    (i : ℕ) (hi : i ≤ x.length) (j : ℤ) (out : List Bool) :
    Cfg (M.k + 1) Bool (satPairTM M).State x :=
  ⟨q.map Sum.inr, ⟨i + 1, by omega⟩,
    fun t => if h : t.val < M.k then saved.workTapes ⟨t, h⟩ else FinTM.bufferTape u,
    fun t => if h : t.val < M.k then saved.workTapePos ⟨t, h⟩ else j, out⟩

/-- Pairing reads native input at the displayed offset. -/
private lemma satPairCfg_input (M : FinTM Bool) {x : List Bool}
    (saved : Cfg M.k Bool M.State x) (u : List Bool) (q : Option (Fin 8))
    (i : ℕ) (hi : i ≤ x.length) (j : ℤ) (out : List Bool) :
    (satPairCfg M saved u q i hi j out).inputSymbol = x[i]? :=
  FinTM.inputSymbol_at _ i hi rfl

/-- Pairing's last work head reads the captured word. -/
private lemma satPairCfg_work (M : FinTM Bool) {x : List Bool}
    (saved : Cfg M.k Bool M.State x) (u : List Bool) (q : Option (Fin 8))
    (i : ℕ) (hi : i ≤ x.length) (j : ℤ) (out : List Bool) :
    (satPairCfg M saved u q i hi j out).workTapeSymbols (Fin.last M.k) =
      FinTM.bufferTape u j := by simp [satPairCfg, Cfg.workTapeSymbols]

/-- Pairing administration changes only the displayed positions and output. -/
private lemma satPairAction_apply (M : FinTM Bool) {x : List Bool}
    (saved : Cfg M.k Bool M.State x) (u : List Bool) (q q' : Option (Fin 8))
    (i i' : ℕ) (hi : i ≤ x.length) (hi' : i' ≤ x.length) (j j' : ℤ)
    (m d : SignType) (b : Option Bool) (out : List Bool)
    (hm : moveInputPos (⟨i + 1, by omega⟩ : Fin (x.length + 2)) m = ⟨i' + 1, by omega⟩)
    (hd : j + d.cast = j') :
    (satPairAction M m d b q').apply (satPairCfg M saved u q i hi j out) =
      satPairCfg M saved u q' i' hi' j' (out ++ b.toList) := by
  refine Cfg.ext rfl hm rfl ?_ rfl
  funext t
  by_cases ht : t.val < M.k
  · simp [satPairAction, satPairCfg, Action.apply, ht]
  · simpa [satPairAction, satPairCfg, Action.apply, ht] using hd

/-- Rewind the captured word from its last occupied cell to the origin.
**Proof sketch.** Induct on the occupied prefix to the left of the head.
Each occupied cell moves left; the blank at `-1` moves right into replay. -/
private lemma satPair_rewind (M : FinTM Bool) {x : List Bool}
    (saved : Cfg M.k Bool M.State x) (u : List Bool) (n : ℕ) (hn : n ≤ u.length) :
    (satPairTM M).tm.runFrom
      (satPairCfg M saved u (some 3) 0 (Nat.zero_le _) ((n : ℤ) - 1) []) (n + 1) =
        satPairCfg M saved u (some 4) 0 (Nat.zero_le _) 0 [] := by
  induction n with
  | zero =>
    rw [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    unfold MultiTapeTM.step
    change ((satPairTM M).tm.tr (.inr 3) _ _).apply _ = _
    simp only [satPairTM]
    rw [satPairCfg_work]
    simp only [Int.natCast_zero, zero_sub, FinTM.bufferTape_left, Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
    exact satPairAction_apply M saved u _ _ 0 0 (Nat.zero_le _) (Nat.zero_le _)
      (-1) 0 0 .pos none [] (moveInputPos_zero _) (by simp)
  | succ n ih =>
    have hw : FinTM.bufferTape u (((n + 1 : ℕ) : ℤ) - 1) = some u[n] := by
      simp [FinTM.bufferTape, List.getElem?_eq_getElem (by omega : n < u.length)]
    have hs : (satPairTM M).tm.step
        (satPairCfg M saved u (some 3) 0 (Nat.zero_le _) (((n + 1 : ℕ) : ℤ) - 1) []) =
        satPairCfg M saved u (some 3) 0 (Nat.zero_le _) ((n : ℤ) - 1) [] := by
      unfold MultiTapeTM.step
      change ((satPairTM M).tm.tr (.inr 3) _ _).apply _ = _
      simp only [satPairTM]
      rw [satPairCfg_work, hw]
      exact satPairAction_apply M saved u _ _ 0 0 (Nat.zero_le _) (Nat.zero_le _)
        _ _ 0 .neg none [] (moveInputPos_zero _) (by simp; omega)
    rw [MultiTapeTM.runFrom_succ_eq_step, hs, ih (by omega)]

/-- Capture through the actual first halt, including a halting emission, then
rewind native input and the captured word. All startup output is suppressed.
**Proof sketch.** Use the audited capture correspondence and native rewind;
the last tape then rewinds across precisely the captured output length. -/
private lemma satPair_start (M : FinTM Bool) (x u : List Bool) (T : ℕ)
    (hM : M.ComputesInTime x u T) :
    ∃ (saved : Cfg M.k Bool M.State x) (s : ℕ), s ≤ T + x.length + u.length + 5 ∧
      (satPairTM M).tm.runFrom ((satPairTM M).tm.initCfg x) s =
        satPairCfg M saved u (some 4) 0 (Nat.zero_le _) 0 [] := by
  obtain ⟨t, ht, hlive, hhalt, hout⟩ := sat_first_halt M x u T hM
  let saved := M.tm.runFrom (M.tm.initCfg x) t
  let captured := captureCfg (Sum.inl : M.State → (satPairTM M).State) (.inr 0) [] [] saved
  have hinit : (satPairTM M).tm.initCfg x =
      captureCfg (Sum.inl : M.State → (satPairTM M).State) (.inr 0) [] [] (M.tm.initCfg x) := by
    refine Cfg.ext rfl rfl ?_ ?_ rfl
    · funext i z; simp [captureCfg, MultiTapeTM.initCfg, Cfg.init, FinTM.bufferTape]
    · funext i; simp [captureCfg, MultiTapeTM.initCfg, Cfg.init]
  have hcap : (satPairTM M).tm.runFrom ((satPairTM M).tm.initCfg x) t = captured := by
    rw [hinit]
    exact capture_run M.tm (satPairTM M).tm Sum.inl (.inr 0) (by intros; rfl)
      [] [] (M.tm.initCfg x) t hlive
  have hstate : captured.state = some (.inr 0) := by
    simp only [captured, captureCfg, saved, hhalt, Option.map_none, Option.getD_none]
  obtain ⟨r, hr, hrew⟩ := FinTM.timed_rewind (satPairTM M).tm (.inr 0) (.inr 1)
    (some (.inr 2)) (by intros; rfl) (by intro inp work; cases inp <;> rfl) captured hstate
  have he : {captured with state := some (.inr 2), inputPos := 1} =
      satPairCfg M saved u (some 2) 0 (Nat.zero_le _) u.length [] := by
    simp only [captured, captureCfg, saved, hout, List.nil_append, satPairCfg, Option.map_some]
    exact Cfg.ext rfl (by apply Fin.ext; simp) rfl rfl rfl
  rw [he] at hrew
  have hs : (satPairTM M).tm.step (satPairCfg M saved u (some 2) 0 (Nat.zero_le _) u.length []) =
      satPairCfg M saved u (some 3) 0 (Nat.zero_le _) ((u.length : ℤ) - 1) [] := by
    change (satPairAction M 0 .neg none (some 3)).apply _ = _
    exact satPairAction_apply M saved u _ _ 0 0 (Nat.zero_le _) (Nat.zero_le _)
      _ _ 0 .neg none [] (moveInputPos_zero _) (by simp; omega)
  refine ⟨saved, t + r + (u.length + 2), ?_, ?_⟩
  · have hp := captured.inputPos.isLt; omega
  · have hpre : (satPairTM M).tm.runFrom ((satPairTM M).tm.initCfg x) (t + r) =
        satPairCfg M saved u (some 2) 0 (Nat.zero_le _) u.length [] := by
      rw [MultiTapeTM.runFrom_add, hcap, hrew]
    rw [MultiTapeTM.runFrom_add, hpre, MultiTapeTM.runFrom_succ_eq_step, hs,
      satPair_rewind M saved u u.length (Nat.le_refl _)]

/-- Replay the captured suffix twice bit by bit and append the pairing
separator. The source bank and native input head remain fixed.
**Proof sketch.** Each occupied capture cell takes two transitions and one
head move. The blank after the word triggers the two fixed separator bits. -/
private lemma satPair_replay (M : FinTM Bool) {x : List Bool}
    (saved : Cfg M.k Bool M.State x) (u rest : List Bool) :
    ∀ pre out, u = pre ++ rest →
      (satPairTM M).tm.runFrom
        (satPairCfg M saved u (some 4) 0 (Nat.zero_le _) pre.length out) (2 * rest.length + 2) =
          satPairCfg M saved u (some 7) 0 (Nat.zero_le _) u.length
            (out ++ satBits rest ++ [false, true]) := by
  induction rest with
  | nil =>
    intro pre out hu
    have he : u = pre := by simpa using hu
    clear hu
    subst u
    have h₁ : (satPairTM M).tm.step
        (satPairCfg M saved pre (some 4) 0 (Nat.zero_le _) pre.length out) =
        satPairCfg M saved pre (some 6) 0 (Nat.zero_le _) pre.length (out ++ [false]) := by
      unfold MultiTapeTM.step
      change ((satPairTM M).tm.tr (.inr 4) _ _).apply _ = _
      simp only [satPairTM]
      rw [satPairCfg_work]
      simp only [FinTM.bufferTape_nat, List.getElem?_length]
      exact satPairAction_apply M saved pre _ _ 0 0 (Nat.zero_le _) (Nat.zero_le _)
        _ _ 0 0 (some false) out (moveInputPos_zero _) (by simp)
    have h₂ : (satPairTM M).tm.step
        (satPairCfg M saved pre (some 6) 0 (Nat.zero_le _) pre.length (out ++ [false])) =
        satPairCfg M saved pre (some 7) 0 (Nat.zero_le _) pre.length ((out ++ [false]) ++ [true]) := by
      exact satPairAction_apply M saved pre _ _ 0 0 (Nat.zero_le _) (Nat.zero_le _)
        _ _ 0 0 (some true) _ (moveInputPos_zero _) (by simp)
    change (satPairTM M).tm.step ((satPairTM M).tm.step _) = _
    rw [h₁, h₂]
    simp [satBits, List.append_assoc]
  | cons b rest ih =>
    intro pre out hu
    have hw : FinTM.bufferTape u (pre.length : ℤ) = some b := by simp [hu]
    have h₁ : (satPairTM M).tm.step
        (satPairCfg M saved u (some 4) 0 (Nat.zero_le _) pre.length out) =
        satPairCfg M saved u (some 5) 0 (Nat.zero_le _) pre.length (out ++ [b]) := by
      unfold MultiTapeTM.step
      change ((satPairTM M).tm.tr (.inr 4) _ _).apply _ = _
      simp only [satPairTM]
      rw [satPairCfg_work, hw]
      exact satPairAction_apply M saved u _ _ 0 0 (Nat.zero_le _) (Nat.zero_le _)
        _ _ 0 0 (some b) out (moveInputPos_zero _) (by simp)
    have h₂ : (satPairTM M).tm.step
        (satPairCfg M saved u (some 5) 0 (Nat.zero_le _) pre.length (out ++ [b])) =
        satPairCfg M saved u (some 4) 0 (Nat.zero_le _) (pre ++ [b]).length (out ++ [b, b]) := by
      unfold MultiTapeTM.step
      change ((satPairTM M).tm.tr (.inr 5) _ _).apply _ = _
      simp only [satPairTM]
      rw [satPairCfg_work, hw]
      simpa [List.append_assoc] using satPairAction_apply M saved u (some 5) (some 4)
        0 0 (Nat.zero_le _) (Nat.zero_le _) (pre.length : ℤ) ((pre ++ [b]).length : ℤ)
        0 .pos (some b) (out ++ [b]) (moveInputPos_zero _) (by simp)
    rw [show 2 * (b :: rest).length + 2 = (2 * rest.length + 2) + 1 + 1 by simp; omega,
      MultiTapeTM.runFrom_succ_eq_step, h₁, MultiTapeTM.runFrom_succ_eq_step, h₂]
    simpa [satBits, List.append_assoc] using ih (pre ++ [b]) (out ++ [b, b])
      (by simpa [List.append_assoc] using hu)

/-- Native suffix copying emits every bit and halts on the right blank.
**Proof sketch.** Induct on the remaining native suffix. Work tapes and heads
are unchanged, including the completed source bank and its captured result. -/
private lemma satPair_copy (M : FinTM Bool) {x : List Bool}
    (saved : Cfg M.k Bool M.State x) (u rest : List Bool) :
    ∀ pre out (hx : x = pre ++ rest),
      (satPairTM M).tm.runFrom
        (satPairCfg M saved u (some 7) pre.length (by simp [hx]) u.length out) (rest.length + 1) =
          satPairCfg M saved u none x.length (Nat.le_refl _) u.length (out ++ rest) := by
  induction rest with
  | nil =>
    intro pre out hx
    have hl : x.length = pre.length := by simp [hx]
    simp only [List.length_nil, Nat.zero_add, MultiTapeTM.runFrom_succ_eq_step,
      MultiTapeTM.runFrom_zero]
    unfold MultiTapeTM.step
    change ((satPairTM M).tm.tr (.inr 7) _ _).apply _ = _
    simp only [satPairTM]
    rw [satPairCfg_input, show x[pre.length]? = none by simp [hx]]
    have ha := satPairAction_apply M saved u (some 7) none pre.length pre.length
      (by omega) (by omega) (u.length : ℤ) (u.length : ℤ) 0 0 none out
      (moveInputPos_zero _) (by simp)
    simpa only [hl, Option.toList_none, List.append_nil] using ha
  | cons b rest ih =>
    intro pre out hx
    have hs : (satPairTM M).tm.step
        (satPairCfg M saved u (some 7) pre.length (by simp [hx]) u.length out) =
        satPairCfg M saved u (some 7) (pre ++ [b]).length (by simp [hx]) u.length (out ++ [b]) := by
      unfold MultiTapeTM.step
      change ((satPairTM M).tm.tr (.inr 7) _ _).apply _ = _
      simp only [satPairTM]
      rw [satPairCfg_input]
      rw [show x[pre.length]? = some b by simp [hx]]
      exact satPairAction_apply M saved u (some 7) (some 7) pre.length (pre ++ [b]).length
        (by simp [hx]) (by simp [hx]) (u.length : ℤ) (u.length : ℤ) .pos 0 (some b) out (by
          simpa using moveInputPos_pos_of_ne_right (⟨pre.length + 1, by simp [hx] <;> omega⟩ : Fin (x.length + 2))
            (by simp [hx] <;> omega)) (by simp)
    simp only [List.length_cons]
    rw [MultiTapeTM.runFrom_succ_eq_step, hs]
    simpa [List.append_assoc] using ih (pre ++ [b]) (out ++ [b])
      (by simpa [List.append_assoc] using hx)

/-- Retaining a computed result next to its original input has a uniform
polynomial overhead; the capture output length is paid by the source time. -/
private lemma satPair_computes (M : FinTM Bool) (f : List Bool → List Bool) (T : ℕ → ℕ)
    (hM : M.ComputesFunInTime f T) :
    (satPairTM M).ComputesFunInTime (fun x => pairEncode (f x) x)
      (fun n => 4 * T n + 2 * n + 8) := by
  intro x
  obtain ⟨saved, s, hs, hstart⟩ := satPair_start M x (f x) (T x.length) (hM x)
  have hrep := satPair_replay M saved (f x) (f x) [] [] (by simp)
  have hcopy := satPair_copy M saved (f x) x [] (satBits (f x) ++ [false, true]) (by simp)
  simp only [List.length_nil, Int.natCast_zero, List.nil_append] at hrep hcopy
  have ht : (f x).length ≤ T x.length := by
    have ho := ((FinTM.computesInTime_iff _ _ _ _).mp (hM x)).2
    simpa only [ho] using M.tm.output_length_le x (T x.length)
  have hc : (satPairTM M).ComputesInTime x (pairEncode (f x) x)
      (s + (2 * (f x).length + 2) + (x.length + 1)) := by
    apply (FinTM.computesInTime_iff _ _ _ _).mpr
    rw [MultiTapeTM.runFrom_add, MultiTapeTM.runFrom_add _ s (2 * (f x).length + 2), hstart, hrep, hcopy]
    exact ⟨rfl, rfl⟩
  exact hc.mono (by dsimp only; omega)

/-- Polynomial-time functions can retain their computed value and the
original input as a pair. -/
private lemma sat_pt_pair_input {f : List Bool → List Bool} (hf : PolyTimeComputable f) :
    PolyTimeComputable (fun x => pairEncode (f x) x) := by
  obtain ⟨M, C, e, hM⟩ := hf
  refine ⟨satPairTM M, 4 * C + 10, e + 1, fun x => (satPair_computes M f _ hM x).mono ?_⟩
  have he : (x.length + 1) ^ e ≤ (x.length + 1) ^ (e + 1) :=
    Nat.pow_le_pow_right (Nat.succ_pos _) (by omega)
  have h1 : x.length + 1 ≤ (x.length + 1) ^ (e + 1) := by
    simpa using Nat.pow_le_pow_right (Nat.succ_pos x.length) (show 1 ≤ e + 1 by omega)
  have ht := Nat.mul_le_mul_left (4 * C) he
  dsimp only
  calc
    _ = 4 * C * (x.length + 1) ^ e + 2 * x.length + 8 := by ring
    _ ≤ 4 * C * (x.length + 1) ^ (e + 1) + 10 * (x.length + 1) ^ (e + 1) := by omega
    _ = _ := by ring

/-- Mapping a paired payload by a polynomial-time function preserves
polynomial time, by the audited data-retaining catalog constructor. -/
private lemma sat_pt_mapSnd {g : List Bool → List Bool} (hg : PolyTimeComputable g) :
    PolyTimeComputable (fun z => match pairDecode z with
      | some (a, b) => pairEncode a (g b)
      | none => []) := by
  obtain ⟨M, C, e, hM⟩ := hg
  obtain ⟨N, K, hN⟩ := FinTM.computesFunInTime_pairMapSnd hM
    (by intro a b hab; exact Nat.mul_le_mul_left C (Nat.pow_le_pow_left (by omega) e))
  refine ⟨N, K * (C + 1), e + 1, fun x => (hN x).mono ?_⟩
  have he : (x.length + 1) ^ e ≤ (x.length + 1) ^ (e + 1) :=
    Nat.pow_le_pow_right (Nat.succ_pos _) (by omega)
  have h1 : x.length + 1 ≤ (x.length + 1) ^ (e + 1) := by
    simpa using Nat.pow_le_pow_right (Nat.succ_pos x.length) (show 1 ≤ e + 1 by omega)
  calc
    _ ≤ K * ((C + 1) * (x.length + 1) ^ (e + 1)) := by
      apply Nat.mul_le_mul_left
      calc
        _ ≤ (x.length + 1) ^ (e + 1) + C * (x.length + 1) ^ (e + 1) :=
          Nat.add_le_add h1 (Nat.mul_le_mul_left C he)
        _ = _ := by ring
    _ = _ := by ring

/-- Independently computed fields can be paired without losing the original
input needed by the second computation. -/
private lemma sat_pt_pair {f g : List Bool → List Bool}
    (hf : PolyTimeComputable f) (hg : PolyTimeComputable g) :
    PolyTimeComputable (fun x => pairEncode (f x) (g x)) := by
  simpa only [Function.comp_def, pairDecode_pairEncode] using
    (sat_pt_mapSnd hg).comp (sat_pt_pair_input hf)

/-- Independently computed word fragments can be concatenated in polynomial time. -/
private lemma sat_pt_append {f g : List Bool → List Bool}
    (hf : PolyTimeComputable f) (hg : PolyTimeComputable g) :
    PolyTimeComputable (fun x => f x ++ g x) := by
  simpa only [Function.comp_def, pairDecode_pairEncode] using
    (sat_pt_linear _ FinTM.computesFunInTime_pairConcat).comp (sat_pt_pair hf hg)

/-- Pure semantics for a finite one-way word transducer with at most one
emitted bit per input bit and one optional final bit. -/
private def satMapWord {S : Type} (next : S → Bool → S)
    (emit : S → Bool → Option Bool) (finish : S → Option Bool) : S → List Bool → List Bool
  | q, [] => (finish q).toList
  | q, b :: r => (emit q b).toList ++ satMapWord next emit finish (next q b) r

/-- Finite one-way transducer for local word operations used by round-field
assembly. It uses no work tapes and always halts at the right boundary. -/
private def satMapTM {S : Type} [Fintype S] [DecidableEq S]
    (next : S → Bool → S) (emit : S → Bool → Option Bool)
    (finish : S → Option Bool) (start : S) : FinTM Bool where
  k := 0
  State := S
  tm := {
    q₀ := start
    tr := fun q inp _ => match inp with
      | some b => ⟨.pos, Fin.elim0, emit q b, some (next q b)⟩
      | none => ⟨0, Fin.elim0, finish q, none⟩ }

/-- Scanner frame with an explicit already-emitted prefix. -/
private def satMapCfg {S : Type} (x : List Bool) (q : S) (i : ℕ)
    (hi : i ≤ x.length) (out : List Bool) : Cfg 0 Bool S x :=
  ⟨some q, ⟨i + 1, by omega⟩, Fin.elim0, Fin.elim0, out⟩

/-- The finite transducer implements its recursive word semantics exactly.
**Proof sketch.** Induct on the unread suffix. An input bit performs one
transition and appends its optional emission; the right blank performs the
final transition, including its optional last bit. -/
private lemma satMap_run {S : Type} [Fintype S] [DecidableEq S]
    (next : S → Bool → S) (emit : S → Bool → Option Bool)
    (finish : S → Option Bool) (start : S) (x rest : List Bool) :
    ∀ pre (hx : x = pre ++ rest) q out,
      ((satMapTM next emit finish start).tm.runFrom
        (satMapCfg x q pre.length (by simp [hx]) out) (rest.length + 1)).state = none ∧
      ((satMapTM next emit finish start).tm.runFrom
        (satMapCfg x q pre.length (by simp [hx]) out) (rest.length + 1)).output =
          out ++ satMapWord next emit finish q rest := by
  induction rest with
  | nil =>
    intro pre hx q out
    simp only [List.append_nil] at hx
    subst x
    simp [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.step, satMapTM,
      satMapCfg, Cfg.inputSymbol, Action.apply, satMapWord]
  | cons b rest ih =>
    intro pre hx q out
    have hs : (satMapTM next emit finish start).tm.step
        (satMapCfg x q pre.length (by simp [hx]) out) =
        satMapCfg x (next q b) (pre ++ [b]).length (by simp [hx]) (out ++ (emit q b).toList) := by
      have hin : (satMapCfg x q pre.length (by simp [hx]) out).inputSymbol = some b := by
        rw [FinTM.inputSymbol_at _ pre.length (by simp [hx]) rfl]
        simp [hx]
      unfold MultiTapeTM.step
      change (((satMapTM next emit finish start).tm.tr q _ _).apply _) = _
      rw [hin]
      refine Cfg.ext_zero_tapes rfl ?_ rfl
      simpa using moveInputPos_pos_of_ne_right
        (⟨pre.length + 1, by simp [hx] <;> omega⟩ : Fin (x.length + 2)) (by simp [hx] <;> omega)
    simp only [List.length_cons]
    rw [MultiTapeTM.runFrom_succ_eq_step, hs]
    simpa only [satMapWord, List.append_assoc] using
      ih (pre ++ [b]) (by simpa [List.append_assoc] using hx) (next q b) (out ++ (emit q b).toList)

/-- Every finite mapper has the exact input-length-plus-one time bound. -/
private lemma satMap_poly {S : Type} [Fintype S] [DecidableEq S]
    (next : S → Bool → S) (emit : S → Bool → Option Bool)
    (finish : S → Option Bool) (start : S) :
    PolyTimeComputable (satMapWord next emit finish start) := by
  refine ⟨satMapTM next emit finish start, 1, 1, fun x => ?_⟩
  apply (FinTM.computesInTime_iff _ _ _ _).mpr
  have hi : (satMapTM next emit finish start).tm.initCfg x =
      satMapCfg x start 0 (Nat.zero_le _) [] := Cfg.ext_zero_tapes rfl rfl rfl
  simpa only [Nat.pow_one, Nat.one_mul, hi, List.length_nil, List.nil_append] using
    satMap_run next emit finish start x x [] (by simp) start []

/-- Replacing every bit by `true` computes the exact unary input length. -/
private lemma sat_pt_unaryLength : PolyTimeComputable (fun x => List.replicate x.length true) := by
  have h := satMap_poly (S := Unit) (fun _ _ => ()) (fun _ _ => some true) (fun _ => none) ()
  have he (x : List Bool) :
      satMapWord (fun (_ : Unit) _ => ()) (fun _ _ => some true) (fun _ => none) () x =
        List.replicate x.length true := by
    induction x with
    | nil => rfl
    | cons b r ih => simpa [satMapWord, List.replicate_succ] using congrArg (true :: ·) ih
  convert h using 1
  funext x
  exact (he x).symm

/-- Removing the first bit is a two-state finite transduction. -/
private lemma sat_pt_tail : PolyTimeComputable List.tail := by
  let emit (q b : Bool) : Option Bool := if q then some b else none
  have h := satMap_poly (fun (_ : Bool) _ => true) emit (fun _ => none) false
  have hc (x : List Bool) : satMapWord (fun (_ : Bool) _ => true) emit (fun _ => none) true x = x := by
    induction x with
    | nil => rfl
    | cons b r ih => simp [satMapWord, emit, ih]
  have he (x : List Bool) : satMapWord (fun (_ : Bool) _ => true) emit (fun _ => none) false x = x.tail := by
    cases x <;> simp [satMapWord, emit, hc]
  convert h using 1
  funext x
  exact (he x).symm

/-- Extracting at most the first bit is also a two-state finite transduction. -/
private lemma sat_pt_head : PolyTimeComputable (fun x => x.take 1) := by
  let emit (q b : Bool) : Option Bool := if q then none else some b
  have h := satMap_poly (fun (_ : Bool) _ => true) emit (fun _ => none) false
  have hc (x : List Bool) : satMapWord (fun (_ : Bool) _ => true) emit (fun _ => none) true x = [] := by
    induction x with
    | nil => rfl
    | cons b r ih => simp [satMapWord, emit, ih]
  have he (x : List Bool) : satMapWord (fun (_ : Bool) _ => true) emit (fun _ => none) false x = x.take 1 := by
    cases x <;> simp [satMapWord, emit, hc]
  convert h using 1
  funext x
  exact (he x).symm

/-- Equality to a fixed control word is decided by the public finite-word
comparison constructor, after any polynomial field computation. -/
private lemma sat_pt_eq {f : List Bool → List Bool} (hf : PolyTimeComputable f) (w : List Bool) :
    PolyTimeComputable (fun x => [decide (f x = w)]) := by
  have he : PolyTimeComputable (fun x => if x = w then [true] else [false]) :=
    sat_pt_linear _ (FinTM.computesFunInTime_ifEq w [true] [false])
  convert he.comp hf using 1
  funext x
  by_cases h : f x = w <;> simp [Function.comp_def, h]

/-- Changing a machine only beyond a guarded stopping point preserves its
entire prefix run. This helper does not assume an eventual halt. -/
private lemma sat_run_agree {k : ℕ} {S : Type} {x : List Bool}
    (A B : MultiTapeTM k Bool S) (c : Cfg k Bool S x) (t : ℕ)
    (h : ∀ i < t, B.step (A.runFrom c i) = A.step (A.runFrom c i)) :
    B.runFrom c t = A.runFrom c t := by
  have hi : ∀ i ≤ t, B.runFrom c i = A.runFrom c i := by
    intro i
    induction i with
    | zero => intro _; rfl
    | succ i ih =>
      intro hit
      rw [MultiTapeTM.runFrom_succ_eq_step', ih (by omega), h i (by omega),
        MultiTapeTM.runFrom_succ_eq_step']
  exact hi t (Nat.le_refl _)

/-- The banked maximum pass has no earlier visit to its streaming entry:
state 9 necessarily emits a bit, whereas the proved endpoint is silent.
**Proof sketch.** If state 9 occurred earlier, the next output would have
positive length. Output-prefix monotonicity would make the silent endpoint
impossible. This justifies intercepting state 9 without redoing the maximum pass. -/
private lemma satRed_start_guard (x : List Bool) (t : ℕ)
    (ho : (satRedTM.tm.runFrom (satRedTM.tm.initCfg x) t).output = []) :
    ∀ i < t, (satRedTM.tm.runFrom (satRedTM.tm.initCfg x) i).state ≠ some (9 : Fin 35) := by
  intro i hi hstate
  have hp := (satRedTM.tm.output_prefix (satRedTM.tm.initCfg x) (show i + 1 ≤ t by omega)).length_le
  rw [ho, List.length_nil, MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.step_output,
    List.length_append] at hp
  have he : (satRedTM.tm.outputSymbol (satRedTM.tm.runFrom (satRedTM.tm.initCfg x) i)).toList.length = 1 := by
    simp only [MultiTapeTM.outputSymbol, hstate]
    simp only [satRedTM]
    split <;> rfl
  rw [he] at hp
  omega

/-- Intercept the proved maximum-pass endpoint and emit its unary cursor.
The earlier banked transition table is used verbatim. Its local buffer marker
is harmless inside this function computation and is erased by a later clean
call; it is never claimed to be a canonical persistent seam. -/
private def satMaxTM : FinTM Bool where
  k := 2
  State := Fin 35
  tm := {
    q₀ := satRedTM.tm.q₀
    tr := fun q inp work =>
      if q = 9 then
        if (work 0).isSome then satRedAction 0 none none .pos 0 (some true) (some 9)
        else satRedAction 0 none none 0 0 none none
      else satRedTM.tm.tr q inp work }

/-- Interception preserves the exact proved initialization and maximum pass. -/
private lemma satMax_start (φ : CNF ℕ) :
    ∃ t ≤ 3 * (CNF.serialize φ).length + 5,
      satMaxTM.tm.runFrom (satMaxTM.tm.initCfg (CNF.serialize φ)) t =
        satRedCfg (CNF.serialize φ) (some 9) 0 (Nat.zero_le _) φ.numVars
          (satRedBuffer [] 0) 0 0 [] := by
  obtain ⟨t, ht, hr⟩ := satRed_start φ
  have hg := satRed_start_guard (CNF.serialize φ) t (by rw [hr]; rfl)
  refine ⟨t, ht, ?_⟩
  have he := sat_run_agree satRedTM.tm satMaxTM.tm (satRedTM.tm.initCfg (CNF.serialize φ)) t (by
    intro i hi
    unfold MultiTapeTM.step
    cases hq : (satRedTM.tm.runFrom (satRedTM.tm.initCfg (CNF.serialize φ)) i).state with
    | none => rfl
    | some q =>
      have hq9 : q ≠ (9 : Fin 35) := by intro h; subst q; exact hg i hi hq
      simp [satMaxTM, hq9])
  exact he.trans hr

/-- Exactly `r` output transitions copy the first `r` unary cursor cells.
No native input or auxiliary buffer movement occurs during replay. -/
private lemma satMax_prefix (x : List Bool) (n : ℕ) (buf : ℤ → Option Bool) :
    ∀ r, r ≤ n → satMaxTM.tm.runFrom
      (satRedCfg x (some 9) 0 (Nat.zero_le _) n buf 0 0 []) r =
        satRedCfg x (some 9) 0 (Nat.zero_le _) n buf r 0 (List.replicate r true) := by
  intro r
  induction r with
  | zero => intro _; rfl
  | succ r ih =>
    intro hr
    rw [MultiTapeTM.runFrom_succ_eq_step', ih (by omega)]
    have hw : (satRedCfg x (some 9) 0 (Nat.zero_le _) n buf r 0
        (List.replicate r true)).workTapeSymbols 0 = some true := by
      simp [satRedCfg, Cfg.workTapeSymbols, satRedCounter_read, show r < n by omega]
    unfold MultiTapeTM.step
    change (satMaxTM.tm.tr (9 : Fin 35) _ _).apply _ = _
    simp only [satMaxTM, ↓reduceIte, hw, Option.isSome_some]
    refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_ ?_
    · funext i z
      by_cases hi : i = 0 <;> simp [satRedAction, satRedCfg, Action.apply, hi]
    · funext i
      simp [satRedAction, satRedCfg, Action.apply]
      split <;> simp [SignType.cast]
    · simp [satRedAction, satRedCfg, Action.apply, List.replicate_succ', List.append_assoc]

/-- The first blank after the copied cursor halts without an extra bit. -/
private lemma satMax_finish (x : List Bool) (n : ℕ) (buf : ℤ → Option Bool) :
    satMaxTM.tm.runFrom (satRedCfg x (some 9) 0 (Nat.zero_le _) n buf 0 0 []) (n + 1) =
      satRedCfg x none 0 (Nat.zero_le _) n buf n 0 (List.replicate n true) := by
  rw [MultiTapeTM.runFrom_succ_eq_step', satMax_prefix x n buf n (Nat.le_refl _)]
  have hw : (satRedCfg x (some 9) 0 (Nat.zero_le _) n buf n 0
      (List.replicate n true)).workTapeSymbols 0 = none := by
    simp [satRedCfg, Cfg.workTapeSymbols, satRedCounter_read]
  unfold MultiTapeTM.step
  change (satMaxTM.tm.tr (9 : Fin 35) _ _).apply _ = _
  simp only [satMaxTM, ↓reduceIte, hw, Option.isSome_none, Bool.false_eq_true]
  refine Cfg.ext rfl (moveInputPos_zero _) ?_ ?_ ?_
  · funext i z; simp [satRedAction, satRedCfg, Action.apply]
  · funext i; simp [satRedAction, satRedCfg, Action.apply]
  · simp [satRedAction, satRedCfg, Action.apply]

/-- The intercepted maximum pass computes the exact unary variable bound on
serialized formulas in linear time, using the existing maximum invariant. -/
private lemma satMax_computes (φ : CNF ℕ) :
    satMaxTM.ComputesInTime (CNF.serialize φ) (List.replicate φ.numVars true)
      (4 * (CNF.serialize φ).length + 6) := by
  obtain ⟨t, ht, hs⟩ := satMax_start φ
  have hn : φ.numVars ≤ (CNF.serialize φ).length := by
    simpa only [CNF.decode_serialize] using CNF.numVars_decode_le (CNF.serialize φ)
  have hc : satMaxTM.ComputesInTime (CNF.serialize φ) (List.replicate φ.numVars true)
      (t + (φ.numVars + 1)) := by
    apply (FinTM.computesInTime_iff _ _ _ _).mpr
    rw [MultiTapeTM.runFrom_add, hs, satMax_finish]
    exact ⟨rfl, rfl⟩
  exact hc.mono (by omega)

/-- Canonicalization uses the full syntax test; invalid strings become the
serialization of the fixed empty-formula fallback. -/
private def satStreamCanonical (x : List Bool) : List Bool :=
  if satSyntax x then x else [false]

/-- The guard implements `serialize ∘ decode` on every input, including
trailing-data failures; it is an actual polynomial-time computation. -/
private lemma satStreamCanonical_spec (x : List Bool) :
    satStreamCanonical x = CNF.serialize (CNF.decode x) := by
  cases hp : CNF.parse x with
  | none => simp [satStreamCanonical, satSyntax_spec, CNF.decode, hp, CNF.fallback, CNF.serialize]
  | some φ => simp [satStreamCanonical, satSyntax_spec, CNF.decode, hp, sat_parse_repr hp, CNF.parse_serialize]

/-- The canonicalizer is a captured conditional over the proved full scanner. -/
private lemma satStreamCanonical_poly : PolyTimeComputable satStreamCanonical :=
  sat_pt_cond satSyntax_poly polyTimeComputable_id (sat_pt_const [false])

/-- The exact unary fresh cursor is polynomial-time computable on all strings.
**Proof sketch.** Canonicalize before running the intercepted maximum pass.
The canonical word has length at most `n+1`; compose on that certified image,
so no behavior of the maximum machine on malformed input is assumed. -/
private lemma sat_pt_numVars : PolyTimeComputable (fun x => List.replicate (CNF.decode x).numVars true) := by
  obtain ⟨M, C, e, hM⟩ := satStreamCanonical_poly
  have hu (x : List Bool) : satMaxTM.ComputesInTime (satStreamCanonical x)
      (List.replicate (CNF.decode x).numVars true) (4 * (x.length + 1) + 6) := by
    rw [satStreamCanonical_spec]
    apply (satMax_computes (CNF.decode x)).mono
    have hl : (CNF.serialize (CNF.decode x)).length ≤ x.length + 1 := by
      rw [← satStreamCanonical_spec]
      unfold satStreamCanonical
      split <;> simp <;> omega
    omega
  obtain ⟨N, hN⟩ := sat_comp_on_image M satMaxTM satStreamCanonical
    (fun x => List.replicate (CNF.decode x).numVars true)
    (fun n => C * (n + 1) ^ e) (fun n => 4 * (n + 1) + 6) hM hu
  refine ⟨N, 2 * C + 12, e + 1, fun x => (hN x).mono ?_⟩
  have he := Nat.mul_le_mul_left (2 * C)
    (Nat.pow_le_pow_right (Nat.succ_pos x.length) (show e ≤ e + 1 by omega))
  have h1 : x.length + 1 ≤ (x.length + 1) ^ (e + 1) := by
    simpa using Nat.pow_le_pow_right (Nat.succ_pos x.length) (show 1 ≤ e + 1 by omega)
  simp only [Nat.succ_eq_add_one] at he
  dsimp only
  calc
    _ = 2 * C * (x.length + 1) ^ e + 4 * (x.length + 1) + 8 := by ring
    _ ≤ 2 * C * (x.length + 1) ^ (e + 1) + 12 * (x.length + 1) ^ (e + 1) := by omega
    _ = _ := by ring

/-- The entire encoded startup word, including the invalid-input offset,
is computable before any clause emission. -/
private lemma satStreamStart_poly : PolyTimeComputable (fun x => satStreamWord (satStreamStart x)) := by
  have hv := sat_pt_pair sat_pt_numVars (sat_pt_pair (sat_pt_const []) (sat_pt_const []))
  have hf := sat_pt_pair (sat_pt_const []) (sat_pt_pair sat_pt_unaryLength (sat_pt_const []))
  have h := sat_pt_cond satSyntax_poly hv hf
  convert h using 1
  funext x
  cases hs : satSyntax x <;> simp [satStreamStart, satStreamWord, hs]

/-- A nonnegative native offset clamped at the right boundary. -/
private def satStreamPos (x : List Bool) (i : ℕ) : Fin (x.length + 2) :=
  ⟨min i x.length + 1, by omega⟩

/-- The clamped offset reads the ordinary optional list entry. -/
private lemma satStreamPos_read {k : ℕ} {S : Type} (x : List Bool)
    (c : Cfg k Bool S x) (i : ℕ) (hi : c.inputPos = satStreamPos x i) :
    c.inputSymbol = x[i]? := by
  rw [FinTM.inputSymbol_at c (min i x.length) (Nat.min_le_right _ _) (by simp [hi, satStreamPos])]
  by_cases h : i ≤ x.length
  · simp [Nat.min_eq_left h]
  · simp [Nat.min_eq_right (by omega : x.length ≤ i), List.getElem?_eq_none (by omega : x.length ≤ i)]

/-- Advancing a clamped offset agrees with an actual right-moving transition,
including repeated requests beyond the native right boundary. -/
private lemma satStreamPos_succ (x : List Bool) (i : ℕ) :
    moveInputPos (satStreamPos x i) .pos = satStreamPos x (i + 1) := by
  by_cases h : i < x.length
  · have he := moveInputPos_pos_of_ne_right (satStreamPos x i)
      (by simp [satStreamPos, Nat.min_eq_left (Nat.le_of_lt h)]; omega)
    rw [he]
    apply Fin.ext
    simp [satStreamPos, Nat.min_eq_left (Nat.le_of_lt h), Nat.min_eq_left (by omega : i + 1 ≤ x.length)]
  · have he : satStreamPos x i = ⟨x.length + 1, by omega⟩ := by
      apply Fin.ext; simp [satStreamPos, Nat.min_eq_right (by omega : x.length ≤ i)]
    rw [he, SignType.pos_eq_one, moveInputPos_rightBoundary]
    apply Fin.ext
    simp [satStreamPos, Nat.min_eq_right (by omega : x.length ≤ i + 1)]

/-- One-tape actions for a length-controlled native suffix extraction. -/
private def satDropAction (m d : SignType) (write : Option (Option Bool))
    (out : Option Bool) (q : Option (Fin 6)) : Action 1 Bool (Fin 6) :=
  ⟨m, fun _ => (write, d), out, q⟩

/-- On `pairEncode u x`, count the doubled prefix on a unary tape, rewind
that tape, skip exactly `|u|` native payload positions with clamping, then
copy the remaining suffix. No output precedes recognition of the separator. -/
private def satDropTM : FinTM Bool where
  k := 1
  State := Fin 6
  tm := {
    q₀ := 0
    tr := fun q inp work => match q.val with
      | 0 => match inp with
        | some b => satDropAction .pos 0 none none (some (if b then 1 else 2))
        | none => satDropAction 0 0 none none none
      | 1 => if inp = some true then satDropAction .pos .pos (some (some true)) none (some 0)
        else satDropAction 0 0 none none none
      | 2 => if inp = some false then satDropAction .pos .pos (some (some true)) none (some 0)
        else if inp = some true then satDropAction .pos .neg none none (some 3)
        else satDropAction 0 0 none none none
      | 3 => if (work 0).isSome then satDropAction 0 .neg none none (some 3)
        else satDropAction 0 .pos none none (some 4)
      | 4 => if (work 0).isSome then satDropAction .pos .pos none none (some 4)
        else satDropAction 0 0 none none (some 5)
      | _ => match inp with
        | some b => satDropAction .pos 0 none (some b) (some 5)
        | none => satDropAction 0 0 none none none }

/-- Counter, counter head, clamped native offset, and emitted prefix. -/
private def satDropCfg (x : List Bool) (q : Option (Fin 6)) (i n : ℕ)
    (h : ℤ) (out : List Bool) : Cfg 1 Bool (Fin 6) x :=
  ⟨q, satStreamPos x i, fun _ => satRedCounter n, fun _ => h, out⟩

/-- A silent dropper action preserves the counter and makes its stated moves. -/
private lemma satDrop_move (x : List Bool) (q q' : Option (Fin 6)) (i i' n : ℕ)
    (h h' : ℤ) (m d : SignType) (b : Option Bool) (out : List Bool)
    (hm : moveInputPos (satStreamPos x i) m = satStreamPos x i') (hd : h + d.cast = h') :
    (satDropAction m d none b q').apply (satDropCfg x q i n h out) =
      satDropCfg x q' i' n h' (out ++ b.toList) := by
  refine Cfg.ext rfl hm rfl ?_ rfl
  funext t
  simpa [satDropAction, satDropCfg, Action.apply] using hd

/-- Writing the counter's right blank appends exactly one unary cell. -/
private lemma satDrop_write (x : List Bool) (q : Option (Fin 6)) (i n : ℕ) :
    (satDropAction .pos .pos (some (some true)) none (some 0)).apply
      (satDropCfg x q i n n []) = satDropCfg x (some 0) (i + 1) (n + 1) (n + 1) [] := by
  refine Cfg.ext rfl (satStreamPos_succ x i) ?_ ?_ rfl
  · funext t z
    simpa [satDropAction, satDropCfg, Action.apply, Nat.max_eq_right (Nat.le_succ n)] using
      congrFun (satRedCounter_write n n (Nat.le_refl _)) z
  · funext t; simp [satDropAction, satDropCfg, Action.apply, SignType.cast]

/-- Each aligned doubled data bit contributes one counter cell in two steps. -/
private lemma satDrop_double (x pre rest : List Bool) (b : Bool) (n : ℕ)
    (hx : x = pre ++ b :: b :: rest) :
    satDropTM.tm.runFrom (satDropCfg x (some 0) pre.length n n []) 2 =
      satDropCfg x (some 0) (pre.length + 2) (n + 1) (n + 1) [] := by
  have hread (q : Option (Fin 6)) (h : ℤ) (j : ℕ) :
      (satDropCfg x q j n h []).inputSymbol = x[j]? := satStreamPos_read x _ j rfl
  have h₁ : satDropTM.tm.step (satDropCfg x (some 0) pre.length n n []) =
      satDropCfg x (some (if b then 1 else 2)) (pre.length + 1) n n [] := by
    unfold MultiTapeTM.step
    change (satDropTM.tm.tr (0 : Fin 6) _ _).apply _ = _
    simp only [satDropTM, hread]
    rw [show x[pre.length]? = some b by simp [hx]]
    exact satDrop_move x _ _ _ _ n _ _ .pos 0 none [] (satStreamPos_succ x _) (by simp)
  have h₂ : satDropTM.tm.step
      (satDropCfg x (some (if b then 1 else 2)) (pre.length + 1) n n []) =
      satDropCfg x (some 0) (pre.length + 2) (n + 1) (n + 1) [] := by
    have hr : x[pre.length + 1]? = some b := by simp [hx]
    cases b <;> unfold MultiTapeTM.step <;>
      simp only [Bool.false_eq_true, ↓reduceIte, satDropTM, hread, hr]
    all_goals exact satDrop_write x _ (pre.length + 1) n
  change satDropTM.tm.step (satDropTM.tm.step _) = _
  rw [h₁, h₂]

/-- The doubled first component is parsed into an exact unary length counter.
**Proof sketch.** Induct on the remaining prefix data, retaining the already
counted prefix. Each aligned pair uses the two-transition lemma. -/
private lemma satDrop_parse (u v : List Bool) :
    ∀ r pre, u = pre ++ r →
      satDropTM.tm.runFrom
        (satDropCfg (pairEncode u v) (some 0) (2 * pre.length) pre.length pre.length []) (2 * r.length) =
          satDropCfg (pairEncode u v) (some 0) (2 * u.length) u.length u.length [] := by
  intro r
  induction r with
  | nil => intro pre hu; simp [hu, MultiTapeTM.runFrom_zero]
  | cons b r ih =>
    intro pre hu
    have hh : pairEncode u v = satBits pre ++ b :: b :: (satBits r ++ [false, true] ++ v) := by
      simp [hu, pairEncode, satBits, List.append_assoc]
    have hs := satDrop_double (pairEncode u v) (satBits pre) (satBits r ++ [false, true] ++ v) b pre.length hh
    simp only [satBits_length] at hs
    rw [show 2 * (b :: r).length = 2 + 2 * r.length by simp; omega,
      MultiTapeTM.runFrom_add, hs]
    have ht := ih (pre ++ [b]) (by simpa [List.append_assoc] using hu)
    simpa [List.length_append, List.length_singleton, Nat.mul_add, Nat.add_assoc] using ht

/-- The aligned `01` separator starts a leftward counter rewind while placing
the native head at the first payload bit. -/
private lemma satDrop_separator (u v : List Bool) :
    satDropTM.tm.runFrom (satDropCfg (pairEncode u v) (some 0) (2 * u.length) u.length u.length []) 2 =
      satDropCfg (pairEncode u v) (some 3) (2 * u.length + 2) u.length ((u.length : ℤ) - 1) [] := by
  have hl : (satBits u).length = 2 * u.length := satBits_length u
  have hr₀ : (pairEncode u v)[2 * u.length]? = some false := by
    rw [← hl]; simp [pairEncode, satBits]
  have hr₁ : (pairEncode u v)[2 * u.length + 1]? = some true := by
    rw [← hl]; simp [pairEncode, satBits]
  have hi (q : Option (Fin 6)) (p : ℕ) (h : ℤ) :
      (satDropCfg (pairEncode u v) q p u.length h []).inputSymbol = (pairEncode u v)[p]? :=
    satStreamPos_read _ _ _ rfl
  have hs : satDropTM.tm.step
      (satDropCfg (pairEncode u v) (some 0) (2 * u.length) u.length u.length []) =
      satDropCfg (pairEncode u v) (some 2) (2 * u.length + 1) u.length u.length [] := by
    unfold MultiTapeTM.step
    change (satDropTM.tm.tr (0 : Fin 6) _ _).apply _ = _
    simp only [satDropTM, hi, hr₀, Bool.false_eq_true, ↓reduceIte]
    exact satDrop_move _ _ _ _ _ _ _ _ .pos 0 none [] (satStreamPos_succ _ _) (by simp)
  change satDropTM.tm.step (satDropTM.tm.step _) = _
  rw [hs]
  unfold MultiTapeTM.step
  change (satDropTM.tm.tr (2 : Fin 6) _ _).apply _ = _
  simp only [satDropTM, hi, hr₁, Option.some.injEq, Bool.true_eq_false, ↓reduceIte]
  exact satDrop_move _ _ _ _ _ _ _ _ .pos .neg none [] (satStreamPos_succ _ _) (by simp; omega)

/-- Counter rewind restores its head without disturbing the payload head. -/
private lemma satDrop_rewind (x : List Bool) (p n : ℕ) :
    ∀ r, r ≤ n → satDropTM.tm.runFrom
      (satDropCfg x (some 3) p n ((r : ℤ) - 1) []) (r + 1) = satDropCfg x (some 4) p n 0 [] := by
  intro r
  induction r with
  | zero =>
    intro _
    simp only [MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    unfold MultiTapeTM.step
    change (satDropTM.tm.tr (3 : Fin 6) _ _).apply _ = _
    have hw : (satDropCfg x (some 3) p n ((0 : ℤ) - 1) []).workTapeSymbols 0 = none := by
      simp [satDropCfg, Cfg.workTapeSymbols, satRedCounter_left]
    simp only [satDropTM, hw, Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
    exact satDrop_move _ _ _ _ _ _ _ _ 0 .pos none [] (moveInputPos_zero _) (by simp)
  | succ r ih =>
    intro hr
    have hw : (satDropCfg x (some 3) p n (((r + 1 : ℕ) : ℤ) - 1) []).workTapeSymbols 0 = some true := by
      have he : (((r + 1 : ℕ) : ℤ) - 1) = r := by omega
      simp [satDropCfg, Cfg.workTapeSymbols, he, satRedCounter_read, show r < n by omega]
    have hs : satDropTM.tm.step (satDropCfg x (some 3) p n (((r + 1 : ℕ) : ℤ) - 1) []) =
        satDropCfg x (some 3) p n ((r : ℤ) - 1) [] := by
      unfold MultiTapeTM.step
      change (satDropTM.tm.tr (3 : Fin 6) _ _).apply _ = _
      simp only [satDropTM, hw, Option.isSome_some, ↓reduceIte]
      exact satDrop_move _ _ _ _ _ _ _ _ 0 .neg none [] (moveInputPos_zero _) (by simp; omega)
    rw [MultiTapeTM.runFrom_succ_eq_step, hs, ih (by omega)]

/-- The unary counter moves the payload head by its stored length. Native
clamping makes this total even when the stored length exceeds the payload. -/
private lemma satDrop_skip (x : List Bool) (p n : ℕ) :
    ∀ r, r ≤ n → satDropTM.tm.runFrom (satDropCfg x (some 4) p n 0 []) r =
      satDropCfg x (some 4) (p + r) n r [] := by
  intro r
  induction r with
  | zero => intro _; simp [MultiTapeTM.runFrom_zero]
  | succ r ih =>
    intro hr
    rw [MultiTapeTM.runFrom_succ_eq_step', ih (by omega)]
    have hw : (satDropCfg x (some 4) (p + r) n r []).workTapeSymbols 0 = some true := by
      simp [satDropCfg, Cfg.workTapeSymbols, satRedCounter_read, show r < n by omega]
    unfold MultiTapeTM.step
    change (satDropTM.tm.tr (4 : Fin 6) _ _).apply _ = _
    simp only [satDropTM, hw, Option.isSome_some, ↓reduceIte]
    simpa only [Nat.add_assoc] using satDrop_move x (some 4) (some 4) (p + r) (p + r + 1)
      n (r : ℤ) ((r + 1 : ℕ) : ℤ) .pos .pos none [] (satStreamPos_succ _ _) (by simp)

/-- Counter exhaustion dispatches to the native copy phase without moving
past the first unconsumed payload bit. -/
private lemma satDrop_dispatch (x : List Bool) (p n : ℕ) :
    satDropTM.tm.step (satDropCfg x (some 4) p n n []) = satDropCfg x (some 5) p n n [] := by
  have hw : (satDropCfg x (some 4) p n n []).workTapeSymbols 0 = none := by
    simp [satDropCfg, Cfg.workTapeSymbols, satRedCounter_read]
  unfold MultiTapeTM.step
  change (satDropTM.tm.tr (4 : Fin 6) _ _).apply _ = _
  simp only [satDropTM, hw, Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
  exact satDrop_move _ _ _ _ _ _ _ _ 0 0 none [] (moveInputPos_zero _) (by simp)

/-- The dropper copies exactly the remaining native suffix and then halts. -/
private lemma satDrop_copy (x rest : List Bool) (n : ℕ) :
    ∀ pre out, x = pre ++ rest →
      satDropTM.tm.runFrom (satDropCfg x (some 5) pre.length n n out) (rest.length + 1) =
        satDropCfg x none x.length n n (out ++ rest) := by
  induction rest with
  | nil =>
    intro pre out hx
    have he : x = pre := by simpa using hx
    clear hx
    subst x
    simp only [List.length_nil, Nat.zero_add, MultiTapeTM.runFrom_succ_eq_step,
      MultiTapeTM.runFrom_zero]
    unfold MultiTapeTM.step
    change (satDropTM.tm.tr (5 : Fin 6) _ _).apply _ = _
    have hin : (satDropCfg pre (some 5) pre.length n n out).inputSymbol = none := by
      rw [satStreamPos_read _ _ _ rfl]; simp
    simp only [satDropTM, hin]
    simpa using satDrop_move _ _ _ _ _ _ _ _ 0 0 none out (moveInputPos_zero _) (by simp)
  | cons b rest ih =>
    intro pre out hx
    have hs : satDropTM.tm.step (satDropCfg x (some 5) pre.length n n out) =
        satDropCfg x (some 5) (pre ++ [b]).length n n (out ++ [b]) := by
      unfold MultiTapeTM.step
      change (satDropTM.tm.tr (5 : Fin 6) _ _).apply _ = _
      have hin : (satDropCfg x (some 5) pre.length n n out).inputSymbol = some b := by
        rw [satStreamPos_read _ _ _ rfl]; simp [hx]
      simp only [satDropTM, hin]
      simpa using satDrop_move x (some 5) (some 5) pre.length (pre.length + 1)
        n (n : ℤ) (n : ℤ) .pos 0 (some b) out (satStreamPos_succ _ _) (by simp)
    rw [List.length_cons, MultiTapeTM.runFrom_succ_eq_step, hs]
    simpa [List.append_assoc] using ih (pre ++ [b]) (out ++ [b])
      (by simpa [List.append_assoc] using hx)

/-- Uniform linear-time suffix extraction from a valid length/data pair.
**Proof sketch.** Parse the doubled prefix, recognize the separator, rewind
its unary counter, and advance once per counter cell. Clamping equates that
endpoint to the split at `min |u| |v|`. Copy the remaining suffix; all earlier
stages are silent, and their lengths sum to the displayed linear envelope. -/
private lemma satDrop_computes (u v : List Bool) :
    satDropTM.ComputesInTime (pairEncode u v) (v.drop u.length)
      (3 * ((pairEncode u v).length + 1)) := by
  let x := pairEncode u v
  let p := 2 * u.length + 2
  let pre := satBits u ++ [false, true] ++ v.take u.length
  have hx : x = pre ++ v.drop u.length := by
    simp [x, pre, pairEncode, satBits, List.append_assoc]
  have hxlen : x.length = p + v.length := by
    change (satBits u ++ [false, true] ++ v).length = _
    simp [p, satBits_length] <;> omega
  have hpre : pre.length = p + min u.length v.length := by simp [pre, p, satBits_length]; omega
  have hpos : satStreamPos x (p + u.length) = satStreamPos x pre.length := by
    apply Fin.ext
    simp only [satStreamPos, hxlen, hpre]
    by_cases h : u.length ≤ v.length
    · simp [Nat.min_eq_left h, Nat.min_eq_left (Nat.add_le_add_left h p)]
    · simp [Nat.min_eq_right (by omega : v.length ≤ u.length),
        Nat.min_eq_right (by omega : p + v.length ≤ p + u.length)]
  have hinit : satDropTM.tm.initCfg x = satDropCfg x (some 0) 0 0 0 [] := by
    refine Cfg.ext rfl ?_ ?_ rfl rfl
    · apply Fin.ext; simp [satDropCfg, satStreamPos, MultiTapeTM.initCfg, Cfg.init]
    · funext i z; simp [satDropCfg, satRedCounter, MultiTapeTM.initCfg, Cfg.init, FinTM.bufferTape]
  have hparse := satDrop_parse u v u [] (by simp)
  simp only [List.length_nil, Nat.mul_zero, Int.natCast_zero] at hparse
  have hstart : satDropTM.tm.runFrom (satDropTM.tm.initCfg x)
      (2 * u.length + 2 + (u.length + 1) + u.length + 1) =
        satDropCfg x (some 5) pre.length u.length u.length [] := by
    rw [MultiTapeTM.runFrom_succ_eq_step', MultiTapeTM.runFrom_add,
      MultiTapeTM.runFrom_add _ (2 * u.length + 2) (u.length + 1),
      MultiTapeTM.runFrom_add _ (2 * u.length) 2, hinit, hparse,
      satDrop_separator, satDrop_rewind _ _ _ u.length (Nat.le_refl _),
      satDrop_skip _ _ _ u.length (Nat.le_refl _), satDrop_dispatch]
    exact Cfg.ext rfl hpos rfl rfl rfl
  have hcopy := satDrop_copy x (v.drop u.length) u.length pre [] hx
  have hc : satDropTM.ComputesInTime x (v.drop u.length)
      (2 * u.length + 2 + (u.length + 1) + u.length + 1 + ((v.drop u.length).length + 1)) := by
    apply (FinTM.computesInTime_iff _ _ _ _).mpr
    rw [MultiTapeTM.runFrom_add, hstart, hcopy]
    exact ⟨rfl, rfl⟩
  apply hc.mono
  change _ ≤ 3 * (x.length + 1)
  rw [hxlen, List.length_drop]
  dsimp only [p]
  omega

/-- Both total field projections are polynomial-time catalog operations. -/
private lemma sat_pt_fields : PolyTimeComputable satStreamFst ∧ PolyTimeComputable satStreamSnd :=
  ⟨sat_pt_linear _ FinTM.computesFunInTime_pairFst,
    sat_pt_linear _ FinTM.computesFunInTime_pairSnd⟩

/-- Suffix extraction is polynomial on every word, with malformed pair
inputs interpreted through the two empty-default projections.
**Proof sketch.** Re-encode the two projections, then use the native dropper
only on that valid-pair image. The re-encoder's proved output bound pays for
the linear dropper run and gives a polynomial original-input envelope. -/
private lemma sat_pt_drop : PolyTimeComputable
    (fun z => (satStreamSnd z).drop (satStreamFst z).length) := by
  let f (z : List Bool) := pairEncode (satStreamFst z) (satStreamSnd z)
  obtain ⟨M, C, e, hM⟩ := sat_pt_pair sat_pt_fields.1 sat_pt_fields.2
  have hlen (z : List Bool) : (f z).length ≤ C * (z.length + 1) ^ e := by
    have ho := ((FinTM.computesInTime_iff _ _ _ _).mp (hM z)).2
    simpa only [ho, f] using M.tm.output_length_le z (C * (z.length + 1) ^ e)
  have hu (z : List Bool) : satDropTM.ComputesInTime (f z)
      ((satStreamSnd z).drop (satStreamFst z).length) (3 * (C * (z.length + 1) ^ e + 1)) :=
    (satDrop_computes _ _).mono (Nat.mul_le_mul_left 3 (Nat.add_le_add_right (hlen z) 1))
  obtain ⟨N, hN⟩ := sat_comp_on_image M satDropTM f
    (fun z => (satStreamSnd z).drop (satStreamFst z).length)
    (fun n => C * (n + 1) ^ e) (fun n => 3 * (C * (n + 1) ^ e + 1)) hM hu
  refine ⟨N, 5 * C + 5, e, fun z => (hN z).mono ?_⟩
  have h1 : 1 ≤ (z.length + 1) ^ e := Nat.one_le_pow _ _ (Nat.succ_pos _)
  dsimp only
  calc
    _ = 5 * C * (z.length + 1) ^ e + 5 := by ring
    _ ≤ 5 * C * (z.length + 1) ^ e + 5 * (z.length + 1) ^ e := by omega
    _ = _ := by ring

/-- The unary-token catalog agrees with the literal serializer's delimiter;
the polarity bit remains the first bit of the returned suffix. -/
private lemma satToken_literal (l : Std.Sat.Literal ℕ) (r : List Bool) :
    unaryTokenSplit (CNF.serializeLit l ++ r) =
      (List.replicate (l.1 + 1) true ++ [false], l.2 :: r) := by
  have ht (k : ℕ) : unaryTokenSplit (List.replicate k true ++ false :: l.2 :: r) =
      (List.replicate k true ++ [false], l.2 :: r) := by
    induction k with
    | zero => rfl
    | succ k ih => simp [List.replicate_succ, unaryTokenSplit, ih]
  simpa [CNF.serializeLit, List.append_assoc] using ht (l.1 + 1)

/-- The token splitter removes just the first delimiter after the true run;
the residual true-run suffix never starts with another true. -/
private lemma satToken_shape (x : List Bool) :
    unaryTokenSplit x =
      (List.replicate (CNF.takeTrues x).1 true ++ (CNF.takeTrues x).2.take 1,
        (CNF.takeTrues x).2.tail) ∧ (CNF.takeTrues x).2.head? ≠ some true := by
  induction x with
  | nil => simp [unaryTokenSplit, CNF.takeTrues]
  | cons b x ih =>
    cases b with
    | false => simp [unaryTokenSplit, CNF.takeTrues]
    | true => simpa [unaryTokenSplit, CNF.takeTrues, ih.1, List.replicate_succ] using ih.2

/-- At a literal marker, a failed literal parse means the token splitter has
no polarity bit. This keeps the total round implementation faithful even on
locally malformed state/input combinations. -/
private lemma satToken_failure (r : List Bool) (hp : CNF.parseLit (true :: r) = none) :
    (unaryTokenSplit (true :: r)).2 = [] := by
  have hs := satToken_shape r
  have ht := (satToken_shape (true :: r)).1
  cases he : CNF.takeTrues r with
  | mk k tail =>
    simp only [he] at hs
    cases tail with
    | nil => simp [ht, CNF.takeTrues, he]
    | cons b rest =>
      cases b with
      | true => exact False.elim (hs.2 rfl)
      | false =>
        cases rest with
        | nil => simp [ht, CNF.takeTrues, he]
        | cons c rest => simp [CNF.parseLit, CNF.takeTrues, he] at hp

/-- Round requests pair the persistent state with a fresh copy of native
input. These projections are read-only word operations. -/
private def satReqFresh (z : List Bool) := satStreamFst (satStreamFst z)
private def satReqUsed (z : List Bool) := satStreamFst (satStreamSnd (satStreamFst z))
private def satReqPhase (z : List Bool) := satStreamSnd (satStreamSnd (satStreamFst z))
private def satReqRest (z : List Bool) := (satStreamSnd z).drop (satReqUsed z).length
private def satReqPol (z : List Bool) := (unaryTokenSplit (satReqRest z)).2
private def satReqLit (z : List Bool) :=
  (unaryTokenSplit (satReqRest z)).1 ++ (satReqPol z).take 1
private def satReqLink (z : List Bool) : Bool :=
  decide (satReqPhase z = List.replicate 3 true) && decide ((satReqPol z).tail.take 1 = [true])

/-- Pair the three canonical fields without any round-local scratch. -/
private def satReqPack (j p : List Bool) (q : ℕ) : List Bool :=
  pairEncode j (pairEncode p (List.replicate q true))

/-- The one larger tail chunk is the audited positive link, two clause
markers, negative link, and the consumed original literal, in that order. -/
private def satReqFragment (z : List Bool) : List Bool :=
  (true :: satReqFresh z) ++ [false, true] ++ [false, true] ++
    (true :: satReqFresh z) ++ [false, false] ++ satReqLit z

/-- A total straight-line word implementation of the round's emitted chunk.
Validation of a complete formula belongs to startup; these local tests only
implement the grammar phase and complete-literal lookahead. -/
private def satReqEmit (z : List Bool) : List Bool :=
  if satReqPhase z = List.replicate 4 true then [] else
  if (satReqRest z).take 1 = [] then [false] else
  if (satReqRest z).take 1 = [false] then [false] else
  if satReqPhase z = [] then [true] else
  if satReqPol z = [] then [] else
  if satReqLink z then satReqFragment z else satReqLit z

/-- The same local tests install the next encoded state. Offset advancement
uses the entire literal length; a fresh allocation happens only on a tail link. -/
private def satReqStep (z : List Bool) : List Bool :=
  let j := satReqFresh z
  let p := satReqUsed z
  let p' := p ++ List.replicate (satReqLit z).length true
  if satReqPhase z = List.replicate 4 true then satStreamFst z else
  if (satReqRest z).take 1 = [] then satReqPack j p 4 else
  if (satReqRest z).take 1 = [false] then
    if satReqPhase z = [] then satReqPack j (p ++ [true]) 4 else satReqPack j (p ++ [true]) 0
  else if satReqPhase z = [] then satReqPack j (p ++ [true]) 1 else
  if satReqPol z = [] then satReqPack j p 4 else
  if satReqLink z then satReqPack (j ++ [true]) p' 3 else
  if satReqPhase z = [true] then satReqPack j p' 2 else satReqPack j p' 3

/-- First-bit word equality and optional-head equality coincide. -/
private lemma sat_take_one_true (x : List Bool) : x.take 1 = [true] ↔ x.head? = some true := by
  cases x <;> simp

/-- Every field of a canonical round request is recovered exactly. -/
private lemma satReq_fields (x : List Bool) (s : SatStreamState) :
    satReqFresh (pairEncode (satStreamWord s) x) = List.replicate s.fresh true ∧
    satReqUsed (pairEncode (satStreamWord s) x) = List.replicate s.used true ∧
    satReqPhase (pairEncode (satStreamWord s) x) = List.replicate s.phase.val true ∧
    satReqRest (pairEncode (satStreamWord s) x) = x.drop s.used := by
  simp [satReqFresh, satReqUsed, satReqPhase, satReqRest, satStreamWord,
    satStreamFst, satStreamSnd, pairDecode_pairEncode]

/-- The word program implements exactly the normalized round, on every
canonical state (not only reachable states).
**Proof sketch.** Split by the phase and the next input item. For a literal,
the token round trip identifies the buffered word and lookahead; if parsing
fails there is no polarity bit. Unary concatenation implements counter
addition. The tail-link branch is precisely the prescribed chunk table. -/
private lemma satReq_round (x : List Bool) (s : SatStreamState) :
    satReqStep (pairEncode (satStreamWord s) x) = satStreamWord (satStreamRound x s).1 ∧
    satReqEmit (pairEncode (satStreamWord s) x) = (satStreamRound x s).2 := by
  obtain ⟨hj, hu, hq, hr⟩ := satReq_fields x s
  cases s with
  | mk j p q =>
    dsimp only at hj hu hq hr
    by_cases h4 : q = 4
    · subst q
      simp [satReqStep, satReqEmit, satReqPhase, satStreamFst, satStreamSnd,
        satStreamWord, pairDecode_pairEncode, satStreamRound]
    · cases hd : x.drop p with
      | nil =>
        simp only [satReqStep, satReqEmit, hj, hu, hq, hr, hd]
        fin_cases q <;> simp_all [satReqPack, satStreamWord, satStreamRound,
          satReqFresh, satReqUsed, satReqPhase, satReqRest, satStreamFst, satStreamSnd,
          pairDecode_pairEncode, List.drop_eq_nil_of_le]
      | cons b r =>
        cases b with
        | false =>
          fin_cases q <;> simp_all [satReqStep, satReqEmit, satReqPack, satStreamWord,
            satStreamRound, List.replicate_succ', List.replicate_succ]
        | true =>
          by_cases h0 : q = 0
          · subst q
            simp only [satReqStep, satReqEmit, hj, hu, hq, hr, hd]
            simp [satReqPack, satStreamWord, satStreamRound, hd, List.replicate_succ']
          · cases hp : CNF.parseLit (true :: r) with
            | none =>
              have hpol : satReqPol (pairEncode (satStreamWord ⟨j, p, q⟩) x) = [] := by
                simp only [satReqPol, hr, hd]
                exact satToken_failure r hp
              fin_cases q <;> simp_all [satReqStep, satReqEmit, satReqPack, satStreamWord, satStreamRound]
            | some lr =>
              rcases lr with ⟨l, rest⟩
              have hrepr := sat_parseLit_repr hp
              have htok := satToken_literal l rest
              rw [← hrepr] at htok
              have hpol : satReqPol (pairEncode (satStreamWord ⟨j, p, q⟩) x) = l.2 :: rest := by
                simp [satReqPol, hr, hd, htok]
              have hlit : satReqLit (pairEncode (satStreamWord ⟨j, p, q⟩) x) = CNF.serializeLit l := by
                simp [satReqLit, hr, hd, htok, hpol, CNF.serializeLit]
              by_cases hnext : rest.head? = some true <;>
                fin_cases q <;> simp_all [satReqStep, satReqEmit, satReqPack, satReqLink, satReqFragment,
                satStreamWord, satStreamRound, sat_take_one_true, List.replicate_add,
                CNF.serializeLit, List.replicate_succ, List.append_assoc] <;>
                rw [← List.replicate_succ', List.replicate_succ]

/-- All read-only request fields and the literal token are polynomial-time
computations, using the audited splitter and the proved native suffix reader. -/
private lemma satReq_fields_poly :
    PolyTimeComputable satReqFresh ∧ PolyTimeComputable satReqUsed ∧
    PolyTimeComputable satReqPhase ∧ PolyTimeComputable satReqRest ∧
    PolyTimeComputable satReqPol ∧ PolyTimeComputable satReqLit := by
  have hj : PolyTimeComputable satReqFresh := sat_pt_fields.1.comp sat_pt_fields.1
  have hu : PolyTimeComputable satReqUsed := sat_pt_fields.1.comp (sat_pt_fields.2.comp sat_pt_fields.1)
  have hq : PolyTimeComputable satReqPhase := sat_pt_fields.2.comp (sat_pt_fields.2.comp sat_pt_fields.1)
  have hr : PolyTimeComputable satReqRest := by
    simpa only [Function.comp_def, satStreamFst, satStreamSnd, pairDecode_pairEncode,
      Option.map_some, Option.getD_some, satReqRest] using
      sat_pt_drop.comp (sat_pt_pair hu sat_pt_fields.2)
  have ht : PolyTimeComputable (fun z => pairEncode (unaryTokenSplit (satReqRest z)).1
      (unaryTokenSplit (satReqRest z)).2) :=
    (sat_pt_linear _ FinTM.computesFunInTime_unaryToken).comp hr
  have hp : PolyTimeComputable satReqPol := by
    simpa only [Function.comp_def, satStreamSnd, pairDecode_pairEncode, Option.map_some,
      Option.getD_some, satReqPol] using sat_pt_fields.2.comp ht
  have hf : PolyTimeComputable (fun z => (unaryTokenSplit (satReqRest z)).1) := by
    simpa only [Function.comp_def, satStreamFst, pairDecode_pairEncode, Option.map_some,
      Option.getD_some] using sat_pt_fields.1.comp ht
  exact ⟨hj, hu, hq, hr, hp, sat_pt_append hf (sat_pt_head.comp hp)⟩

/-- Canonical field packing preserves polynomial time for every fixed tag. -/
private lemma sat_pt_pack {j p : List Bool → List Bool} (hj : PolyTimeComputable j)
    (hp : PolyTimeComputable p) (q : ℕ) : PolyTimeComputable (fun z => satReqPack (j z) (p z) q) :=
  sat_pt_pair hj (sat_pt_pair hp (sat_pt_const _))

/-- The Boolean tail-link decision is a conjunction of two finite-word tests. -/
private lemma satReqLink_poly : PolyTimeComputable (fun z => [satReqLink z]) := by
  obtain ⟨_, _, hq, _, hp, _⟩ := satReq_fields_poly
  exact sat_pt_and (sat_pt_eq hq _) (sat_pt_eq (sat_pt_head.comp (sat_pt_tail.comp hp)) [true])

/-- The tail fragment is built by a fixed number of polynomial concatenations. -/
private lemma satReqFragment_poly : PolyTimeComputable satReqFragment := by
  obtain ⟨hj, _, _, _, _, hl⟩ := satReq_fields_poly
  have hvar : PolyTimeComputable (fun z => true :: satReqFresh z) :=
    (sat_pt_linear _ (FinTM.computesFunInTime_prepend [true])).comp hj
  exact sat_pt_append (sat_pt_append (sat_pt_append
    (sat_pt_append (sat_pt_append hvar (sat_pt_const [false, true]))
      (sat_pt_const [false, true])) hvar) (sat_pt_const [false, false])) hl

/-- The per-round output chunk has an actual polynomial-time finite-machine
witness, including empty finished chunks and the invalid-input fallback. -/
private lemma satReqEmit_poly : PolyTimeComputable satReqEmit := by
  obtain ⟨_, _, hq, hr, hp, hl⟩ := satReq_fields_poly
  have hh := sat_pt_head.comp hr
  have h := sat_pt_cond (sat_pt_eq hq (List.replicate 4 true)) (sat_pt_const [])
    (sat_pt_cond (sat_pt_eq hh []) (sat_pt_const [false])
      (sat_pt_cond (sat_pt_eq hh [false]) (sat_pt_const [false])
        (sat_pt_cond (sat_pt_eq hq []) (sat_pt_const [true])
          (sat_pt_cond (sat_pt_eq hp []) (sat_pt_const [])
            (sat_pt_cond satReqLink_poly satReqFragment_poly hl)))))
  simpa only [satReqEmit, Function.comp_def, decide_eq_true_eq] using h

/-- The next persistent state also has an actual polynomial-time witness;
all branch tests are computed and captured on the original round request. -/
private lemma satReqStep_poly : PolyTimeComputable satReqStep := by
  obtain ⟨hj, hu, hq, hr, hp, hl⟩ := satReq_fields_poly
  have hu1 := sat_pt_append hu (sat_pt_const [true])
  have hj1 := sat_pt_append hj (sat_pt_const [true])
  have hul := sat_pt_append hu (sat_pt_unaryLength.comp hl)
  have hh := sat_pt_head.comp hr
  have h := sat_pt_cond (sat_pt_eq hq (List.replicate 4 true)) sat_pt_fields.1
    (sat_pt_cond (sat_pt_eq hh []) (sat_pt_pack hj hu 4)
      (sat_pt_cond (sat_pt_eq hh [false])
        (sat_pt_cond (sat_pt_eq hq []) (sat_pt_pack hj hu1 4) (sat_pt_pack hj hu1 0))
        (sat_pt_cond (sat_pt_eq hq []) (sat_pt_pack hj hu1 1)
          (sat_pt_cond (sat_pt_eq hp []) (sat_pt_pack hj hu 4)
            (sat_pt_cond satReqLink_poly (sat_pt_pack hj1 hul 3)
              (sat_pt_cond (sat_pt_eq hq [true]) (sat_pt_pack hj hul 2) (sat_pt_pack hj hul 3)))))))
  simpa only [satReqStep, Function.comp_def, decide_eq_true_eq] using h

/-- A marker-free administrative pass appends the native input to tape zero,
then rewinds both heads. It is used to form a round request and at startup.
The only occupied tape is the data tape; no origin marker is introduced. -/
private def satAppendTM : FinTM Bool where
  k := 1
  State := Fin 5
  tm := {
    q₀ := 0
    tr := fun q inp work => match q.val with
      | 0 => if (work 0).isSome then ⟨0, fun _ => (none, .pos), none, some 0⟩
        else ⟨0, fun _ => (none, 0), none, some 1⟩
      | 1 => match inp with
        | some b => ⟨.pos, fun _ => (some (some b), .pos), none, some 1⟩
        | none => ⟨0, fun _ => (none, .neg), none, some 2⟩
      | 2 => if (work 0).isSome then ⟨0, fun _ => (none, .neg), none, some 2⟩
        else ⟨0, fun _ => (none, .pos), none, some 3⟩
      | 3 => FinTM.controlAction .neg (some 4)
      | _ => match inp with
        | some _ => FinTM.controlAction .neg (some 4)
        | none => FinTM.controlAction .pos none }

/-- The appender's complete configuration, with no hidden scratch. -/
private def satAppendCfg (x : List Bool) (q : Option (Fin 5))
    (i : Fin (x.length + 2)) (w : List Bool) (h : ℤ) : Cfg 1 Bool (Fin 5) x :=
  ⟨q, i, fun _ => FinTM.bufferTape w, fun _ => h, []⟩

/-- Seek the first blank after a known word, without moving the native head.
**Proof sketch.** Each occupied cell advances once; the right blank dispatches
in one further transition. -/
private lemma satAppend_seek (x w rest : List Bool) :
    ∀ pre, w = pre ++ rest → satAppendTM.tm.runFrom
      (satAppendCfg x (some 0) 1 w pre.length) (rest.length + 1) =
        satAppendCfg x (some 1) 1 w w.length := by
  induction rest with
  | nil =>
    intro pre hw
    have he : w = pre := by simpa using hw
    subst w
    simp only [List.length_nil, Nat.zero_add, MultiTapeTM.runFrom_succ_eq_step,
      MultiTapeTM.runFrom_zero]
    unfold MultiTapeTM.step
    change (satAppendTM.tm.tr (0 : Fin 5) _ _).apply _ = _
    simp [satAppendTM, satAppendCfg, Cfg.workTapeSymbols, Action.apply]
  | cons b rest ih =>
    intro pre hw
    have hs : satAppendTM.tm.step (satAppendCfg x (some 0) 1 w pre.length) =
        satAppendCfg x (some 0) 1 w (pre ++ [b]).length := by
      unfold MultiTapeTM.step
      change (satAppendTM.tm.tr (0 : Fin 5) _ _).apply _ = _
      have hr : (satAppendCfg x (some 0) 1 w pre.length).workTapeSymbols 0 = some b := by
        simp [satAppendCfg, Cfg.workTapeSymbols, hw]
      simp only [satAppendTM]
      rw [hr]
      simp [satAppendCfg, Action.apply, SignType.cast, sub_eq_add_neg, add_assoc]
    rw [show (b :: rest).length + 1 = (rest.length + 1) + 1 by simp,
      MultiTapeTM.runFrom_succ_eq_step, hs]
    exact ih (pre ++ [b]) (by simpa [List.append_assoc] using hw)

/-- Native copying appends at the right blank and enters the work-tape rewind.
**Proof sketch.** The append lemma identifies the full infinite tape after
each write; clamped native positions advance through the remaining suffix. -/
private lemma satAppend_copy (x w rest : List Bool) :
    ∀ pre, x = pre ++ rest → satAppendTM.tm.runFrom
      (satAppendCfg x (some 1) (satStreamPos x pre.length) (w ++ pre) (w ++ pre).length)
      (rest.length + 1) =
        satAppendCfg x (some 2) (satStreamPos x x.length) (w ++ x) ((w ++ x).length - 1) := by
  induction rest with
  | nil =>
    intro pre hx
    have he : x = pre := by simpa using hx
    clear hx
    subst x
    simp only [List.length_nil, Nat.zero_add, MultiTapeTM.runFrom_succ_eq_step,
      MultiTapeTM.runFrom_zero]
    have hr := satStreamPos_read pre (satAppendCfg pre (some 1)
      (satStreamPos pre pre.length) (w ++ pre) (w ++ pre).length) pre.length rfl
    unfold MultiTapeTM.step
    change (satAppendTM.tm.tr (1 : Fin 5) _ _).apply _ = _
    simp only [satAppendTM, hr, List.getElem?_length]
    refine Cfg.ext rfl (moveInputPos_zero _) rfl ?_ rfl
    funext i
    simp [satAppendCfg, Action.apply, SignType.cast, sub_eq_add_neg, add_assoc]
  | cons b rest ih =>
    intro pre hx
    have hs : satAppendTM.tm.step
        (satAppendCfg x (some 1) (satStreamPos x pre.length) (w ++ pre) (w ++ pre).length) =
        satAppendCfg x (some 1) (satStreamPos x (pre ++ [b]).length)
          (w ++ (pre ++ [b])) (w ++ (pre ++ [b])).length := by
      have hr : (satAppendCfg x (some 1) (satStreamPos x pre.length)
          (w ++ pre) (w ++ pre).length).inputSymbol = some b := by
        rw [satStreamPos_read x _ pre.length rfl]
        simp [hx]
      unfold MultiTapeTM.step
      change (satAppendTM.tm.tr (1 : Fin 5) _ _).apply _ = _
      simp only [satAppendTM, hr, List.getElem?_cons_zero]
      refine Cfg.ext rfl ?_ ?_ ?_ rfl
      · simpa using satStreamPos_succ x pre.length
      · funext i
        simpa [satAppendCfg, Action.apply, List.append_assoc] using
          (FinTM.bufferTape_append (w ++ pre) b).symm
      · funext i; simp [satAppendCfg, Action.apply, SignType.cast, sub_eq_add_neg, add_assoc]
    rw [show (b :: rest).length + 1 = (rest.length + 1) + 1 by simp,
      MultiTapeTM.runFrom_succ_eq_step, hs]
    exact ih (pre ++ [b]) (by simpa [List.append_assoc] using hx)

/-- Rewind exactly the occupied prefix, using its left blank only locally.
**Proof sketch.** Induction on the number of cells to the left of the head;
the blank at minus one is never written, and the final head is zero. -/
private lemma satAppend_rewind (x w : List Bool) (i : Fin (x.length + 2)) :
    ∀ r, r ≤ w.length → satAppendTM.tm.runFrom
      (satAppendCfg x (some 2) i w ((r : ℤ) - 1)) (r + 1) =
        satAppendCfg x (some 3) i w 0 := by
  intro r
  induction r with
  | zero =>
    intro _
    simp only [Nat.zero_add, MultiTapeTM.runFrom_succ_eq_step, MultiTapeTM.runFrom_zero]
    unfold MultiTapeTM.step
    change (satAppendTM.tm.tr (2 : Fin 5) _ _).apply _ = _
    have hr : (satAppendCfg x (some 2) i w ((0 : ℤ) - 1)).workTapeSymbols 0 = none := by
      simp [satAppendCfg, Cfg.workTapeSymbols, FinTM.bufferTape]
    simp only [satAppendTM]
    simp only [Nat.cast_zero]
    rw [hr]
    simp [satAppendCfg, Action.apply, SignType.cast, sub_eq_add_neg, add_assoc]
  | succ r ih =>
    intro hr
    have hs : satAppendTM.tm.step (satAppendCfg x (some 2) i w (((r + 1 : ℕ) : ℤ) - 1)) =
        satAppendCfg x (some 2) i w ((r : ℤ) - 1) := by
      have hw : ((satAppendCfg x (some 2) i w (((r + 1 : ℕ) : ℤ) - 1)).workTapeSymbols 0).isSome = true := by
        simp [satAppendCfg, Cfg.workTapeSymbols, FinTM.bufferTape_nat, List.getElem?_eq_getElem (by omega : r < w.length)]
      unfold MultiTapeTM.step
      change (satAppendTM.tm.tr (2 : Fin 5) _ _).apply _ = _
      simp only [satAppendTM]
      rw [hw]
      simp [satAppendCfg, Action.apply, SignType.cast, sub_eq_add_neg, add_assoc]
    rw [MultiTapeTM.runFrom_succ_eq_step, hs]
    exact ih (by omega)

/-- A padded halting run can be cut at its first halt without changing any
endpoint field. This is the local instance of the engine's minimal-halt
argument: use `Nat.find` and the absorbing-halt law. -/
private lemma sat_call_first_halt {k : ℕ} {S : Type} {x : List Bool}
    (tm : MultiTapeTM k Bool S) (cfg : Cfg k Bool S x) (t : ℕ)
    (hstart : cfg.state ≠ none) (hhalt : (tm.runFrom cfg t).state = none) :
    ∃ u, 0 < u ∧ u ≤ t ∧ (∀ v < u, ¬(tm.runFrom cfg v).Halted) ∧
      tm.runFrom cfg u = tm.runFrom cfg t := by
  classical
  let h : ∃ u, (tm.runFrom cfg u).state = none := ⟨t, hhalt⟩
  have hu := Nat.find_spec h
  have hle := Nat.find_min' h hhalt
  refine ⟨Nat.find h, ?_, hle, fun v hv => Nat.find_min h hv, ?_⟩
  · by_contra hn
    have hz : Nat.find h = 0 := by omega
    rw [hz, MultiTapeTM.runFrom_zero] at hu
    exact hstart hu
  · symm
    rw [← Nat.add_sub_of_le hle, MultiTapeTM.runFrom_add, MultiTapeTM.runFrom_of_halt _ hu]

/-- The appender has a full clean return, in linear time in the native input
and existing word. Both input and work heads return to their canonical origins.
**Proof sketch.** Compose seek, copy, work rewind, and the audited native
rewind. Choose the first halt so forwarding wrappers may use the run directly. -/
private lemma satAppend_clean (x w : List Bool) :
    ∃ t, 0 < t ∧ t ≤ 2 * w.length + 3 * x.length + 6 ∧
      (∀ v < t, ¬(satAppendTM.tm.runFrom
        (Cfg.ofWords (input := x) (0 : Fin 5) (stateWord 1 w)) v).Halted) ∧
      satAppendTM.tm.runFrom (Cfg.ofWords (input := x) (0 : Fin 5) (stateWord 1 w)) t =
        { Cfg.ofWords (input := x) (0 : Fin 5) (stateWord 1 (w ++ x)) with state := none } := by
  have hs := satAppend_seek x w w [] (by simp)
  have hc := satAppend_copy x w x [] (by simp)
  have hr := satAppend_rewind x (w ++ x) (satStreamPos x x.length) (w ++ x).length (Nat.le_refl _)
  obtain ⟨r, hb, hn⟩ := FinTM.timed_rewind satAppendTM.tm (3 : Fin 5) (4 : Fin 5) none
    (by intros; rfl) (by intro inp work; cases inp <;> rfl)
    (satAppendCfg x (some 3) (satStreamPos x x.length) (w ++ x) 0) rfl
  have hi : Cfg.ofWords (input := x) (0 : Fin 5) (stateWord 1 w) = satAppendCfg x (some 0) 1 w 0 := by
    refine Cfg.ext rfl rfl ?_ rfl rfl
    funext i; fin_cases i; rfl
  have he : satAppendTM.tm.runFrom (Cfg.ofWords (input := x) (0 : Fin 5) (stateWord 1 w))
      (w.length + 1 + (x.length + 1) + ((w ++ x).length + 1) + r) =
      { Cfg.ofWords (input := x) (0 : Fin 5) (stateWord 1 (w ++ x)) with state := none } := by
    rw [hi, MultiTapeTM.runFrom_add _ _ r,
      MultiTapeTM.runFrom_add _ _ ((w ++ x).length + 1),
      MultiTapeTM.runFrom_add _ (w.length + 1) (x.length + 1)]
    simp only [List.length_nil, Nat.cast_zero] at hs
    rw [hs]
    have hp : satStreamPos x 0 = 1 := by apply Fin.ext; simp [satStreamPos]
    simp only [List.length_nil, List.append_nil, hp] at hc
    rw [hc, hr, hn]
    refine Cfg.ext rfl rfl ?_ rfl rfl
    funext i; fin_cases i; rfl
  obtain ⟨u, hu, hut, hg, heq⟩ := sat_call_first_halt satAppendTM.tm
    (Cfg.ofWords (input := x) (0 : Fin 5) (stateWord 1 w)) _ (by simp [Cfg.ofWords])
    (by rw [he])
  refine ⟨u, hu, ?_, hg, heq.trans he⟩
  simp only [satAppendCfg, satStreamPos, Nat.min_self] at hb
  simp only [List.length_append] at hut
  omega

/-- Pad a callable module into a shared bank, keeping unused tapes stationary. -/
private def satPadAction {k K : ℕ} {S : Type} (a : Action k Bool S) : Action K Bool S :=
  ⟨a.inputTape, fun i => if h : i.val < k then a.workTapes ⟨i.val, h⟩ else (none, 0),
    a.output, a.state⟩

/-- All modules share tape zero; a positive source bank is padded on the right. -/
private def satPadTM (M : FinTM Bool) (K : ℕ) (hk : M.k ≤ K) : FinTM Bool where
  k := K
  State := M.State
  tm := { q₀ := M.tm.q₀
          tr := fun q inp work => satPadAction (M.tm.tr q inp
            (fun i => work ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩)) }

/-- Configuration embedding for the shared bank; the padding is genuinely blank. -/
private def satPadCfg {k K : ℕ} {S : Type} {x : List Bool}
    (c : Cfg k Bool S x) : Cfg K Bool S x :=
  ⟨c.state, c.inputPos,
    fun i => if h : i.val < k then c.workTapes ⟨i.val, h⟩ else fun _ => none,
    fun i => if h : i.val < k then c.workTapePos ⟨i.val, h⟩ else 0, c.output⟩

/-- Padding commutes with a transition, including writes at arbitrary cells.
**Proof sketch.** Split each work index by membership in the source bank;
the inactive branch neither writes nor moves. -/
private lemma satPad_apply {k K : ℕ} {S : Type} {x : List Bool}
    (a : Action k Bool S) (c : Cfg k Bool S x) :
    (satPadAction (K := K) a).apply (satPadCfg c) = satPadCfg (a.apply c) := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  · funext i z
    by_cases h : i.val < k <;> simp [satPadAction, satPadCfg, Action.apply, h]
  · funext i
    by_cases h : i.val < k <;> simp [satPadAction, satPadCfg, Action.apply, h]

/-- The padded source observes exactly its original work symbols. -/
private lemma satPad_run (M : FinTM Bool) (K : ℕ) (hk : M.k ≤ K)
    {x : List Bool} (c : Cfg M.k Bool M.State x) (t : ℕ) :
    (satPadTM M K hk).tm.runFrom (satPadCfg c) t = satPadCfg (M.tm.runFrom c t) := by
  apply MultiTapeTM.runFrom_comm_of_step
  intro c
  cases hs : c.state with
  | none => simp [MultiTapeTM.step, satPadCfg, hs]
  | some q =>
    have hw : (fun i : Fin M.k => (satPadCfg (K := K) c).workTapeSymbols
        ⟨i.val, Nat.lt_of_lt_of_le i.isLt hk⟩) = c.workTapeSymbols := by
      funext i; simp [satPadCfg, Cfg.workTapeSymbols, i.isLt]
    have hstate : (satPadCfg (K := K) c).state = some q := hs
    simp only [MultiTapeTM.step, hstate, hs]
    change (satPadAction (M.tm.tr q c.inputSymbol _)).apply _ = _
    rw [hw]
    exact satPad_apply _ _

/-- Positive tape count makes the padded seam the same canonical state word. -/
private lemma satPad_seam {k K : ℕ} {S : Type} {x : List Bool}
    (hk : 0 < k) (q : S) (w out : List Bool) :
    satPadCfg (K := K) ({Cfg.ofWords (input := x) q (stateWord k w) with output := out}) =
      {Cfg.ofWords (input := x) q (stateWord K w) with output := out} := by
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  · funext i z
    by_cases hi : i.val < k
    · simp [satPadCfg, Cfg.ofWords, stateWord, hi]
    · have hn : i.val ≠ 0 := by omega
      simp [satPadCfg, Cfg.ofWords, stateWord, hi, hn, FinTM.bufferTape]
  · funext i
    by_cases hi : i.val < k <;> simp [satPadCfg, Cfg.ofWords, hi]

/-- Convert a first-positive-exit module into a halting source for `emit_run`.
The Boolean release flag ensures even an entry equal to exit executes once. -/
private def satStopTM (C : FinTM Bool) (entry exit : C.State) : FinTM Bool where
  k := C.k
  State := Bool × C.State
  tm := { q₀ := (false, entry)
          tr := fun q inp work =>
            if q.1 = true ∧ q.2 = exit then FinTM.controlAction 0 none
            else {C.tm.tr q.2 inp work with state := (C.tm.tr q.2 inp work).state.map (true, ·)} }

/-- Release-flag embedding preserves all physical fields of a call. -/
private def satStopCfg {k : ℕ} {S : Type} {x : List Bool}
    (b : Bool) (c : Cfg k Bool S x) : Cfg k Bool (Bool × S) x :=
  ⟨c.state.map (b, ·), c.inputPos, c.workTapes, c.workTapePos, c.output⟩

/-- Before the designated positive exit, the stopped source takes the same
physical step as the module and raises the release flag. -/
private lemma satStop_step (C : FinTM Bool) (entry exit : C.State)
    {x : List Bool} (b : Bool) (c : Cfg C.k Bool C.State x)
    (hlive : c.state ≠ none) (hg : b = true → c.state ≠ some exit) :
    (satStopTM C entry exit).tm.step (satStopCfg b c) = satStopCfg true (C.tm.step c) := by
  cases hs : c.state with
  | none => exact False.elim (hlive hs)
  | some q =>
    have hq : ¬(b = true ∧ q = exit) := by
      rintro ⟨hb, rfl⟩; exact hg hb hs
    simp only [MultiTapeTM.step, satStopCfg, hs, Option.map_some]
    simp only [satStopTM, hq, ↓reduceIte]
    rfl

/-- Live endpoints force every earlier module state to be live. -/
private lemma sat_live_prefix {k : ℕ} {S : Type} {x : List Bool}
    (tm : MultiTapeTM k Bool S) (c : Cfg k Bool S x) (t : ℕ)
    (ht : (tm.runFrom c t).state ≠ none) :
    ∀ u ≤ t, (tm.runFrom c u).state ≠ none := by
  intro u hu hh
  have he : tm.runFrom c t = tm.runFrom c u := by
    rw [← Nat.add_sub_of_le hu, MultiTapeTM.runFrom_add, MultiTapeTM.runFrom_of_halt _ hh]
  exact ht (by rw [he]; exact hh)

/-- Stop a clean call one silent step after its certified first positive exit.
**Proof sketch.** Induct on prefixes, keeping the release flag false only at
time zero. The supplied guard prevents early stopping; a final silent halt
retains every canonical seam field and every emitted bit. -/
private lemma satStop_clean (C : FinTM Bool) (entry exit : C.State)
    (x arg result out : List Bool) (t : ℕ) (ht : 0 < t)
    (hg : ∀ v, 0 < v → v < t → (C.tm.runFrom
      (Cfg.ofWords (input := x) entry (stateWord C.k arg)) v).state ≠ some exit)
    (he : C.tm.runFrom (Cfg.ofWords (input := x) entry (stateWord C.k arg)) t =
      {Cfg.ofWords exit (stateWord C.k result) with output := out}) :
    (satStopTM C entry exit).tm.runFrom
      (Cfg.ofWords (input := x) (false, entry) (stateWord C.k arg)) (t + 1) =
      {Cfg.ofWords (true, exit) (stateWord C.k result) with state := none, output := out} := by
  let c := Cfg.ofWords (input := x) entry (stateWord C.k arg)
  have hl := sat_live_prefix C.tm c t (by rw [show C.tm.runFrom c t = _ from he]; simp [Cfg.ofWords])
  have hp : ∀ v, v ≤ t → (satStopTM C entry exit).tm.runFrom (satStopCfg false c) v =
      satStopCfg (decide (v ≠ 0)) (C.tm.runFrom c v) := by
    intro v
    induction v with
    | zero => intro _; rfl
    | succ v ih =>
      intro hv
      rw [MultiTapeTM.runFrom_succ_eq_step', ih (by omega),
        satStop_step C entry exit _ _ (hl v (by omega)) (by
          intro hn
          exact hg v (Nat.pos_of_ne_zero (of_decide_eq_true hn)) (by omega)),
        MultiTapeTM.runFrom_succ_eq_step']
      rfl
  have hi : Cfg.ofWords (input := x) (false, entry) (stateWord C.k arg) = satStopCfg false c := rfl
  rw [hi, MultiTapeTM.runFrom_succ_eq_step', hp t (Nat.le_refl _)]
  have hflag : decide (t ≠ 0) = true := by simp [Nat.ne_of_gt ht]
  rw [hflag, show C.tm.runFrom c t = _ from he]
  simp [MultiTapeTM.step, satStopTM, satStopCfg, Cfg.ofWords, FinTM.controlAction, Action.apply]

/-- Six finite modules form the streaming body: startup append and install,
then the recurring pack, append, emit, and install calls. -/
private abbrev SatHostState (M : Fin 6 → FinTM Bool) := Unit ⊕ (Σ i, (M i).State)

/-- A module's return destination; startup install and step install return to
the unique loop anchor. The other calls continue to the next finite module. -/
private def satHostNext (i : Fin 6) : Option (Fin 6) :=
  if i = 0 then some 1 else if i = 2 then some 3 else if i = 3 then some 4
  else if i = 4 then some 5 else none

/-- A named entry state inside the finite body. -/
private def satHostEntry (M : Fin 6 → FinTM Bool) (i : Fin 6) : SatHostState M :=
  .inr ⟨i, (M i).tm.q₀⟩

/-- Resolve a finite module's return, with no additional tape operation. -/
private def satHostRet (M : Fin 6 → FinTM Bool) (i : Fin 6) : SatHostState M :=
  match satHostNext i with
  | some j => satHostEntry M j
  | none => .inl ()

/-- The actual finite controller. All modules use the same padded work bank,
so the clean-call contracts restore scratch before each next call. `emitAction`
forwards the halting transition as well as ordinary transitions. -/
private def satHostTM (M : Fin 6 → FinTM Bool) (K : ℕ) (hk : ∀ i, (M i).k ≤ K) : FinTM Bool where
  k := K
  State := SatHostState M
  tm := {
    q₀ := satHostEntry M 0
    tr := fun q inp work => match q with
      | .inl _ => FinTM.controlAction 0 (some (satHostEntry M 2))
      | .inr ⟨i, s⟩ => emitAction (fun s => .inr ⟨i, s⟩) (satHostRet M i)
          ((satPadTM (M i) K (hk i)).tm.tr s inp work) }

/-- Forwarding a padded clean configuration produces the host's canonical
seam with precisely the supplied output prefix. Positive tape count is used
only to identify the real tape-zero word. -/
private lemma satHost_seam (M : Fin 6 → FinTM Bool) (K : ℕ) (i : Fin 6)
    (hp : 0 < (M i).k) (x w pre out : List Bool) (q : (M i).State)
    (state : Option (M i).State) :
    emitCfg (fun s => (Sum.inr ⟨i, s⟩ : SatHostState M)) (satHostRet M i) pre
      (satPadCfg (K := K) {Cfg.ofWords (input := x) q (stateWord (M i).k w)
        with state := state, output := out}) =
      {Cfg.ofWords (((state.map (fun s => (Sum.inr ⟨i, s⟩ : SatHostState M))).getD (satHostRet M i)))
        (stateWord K w) with output := pre ++ out} := by
  have h := satPad_seam (K := K) (x := x) hp q w out
  refine Cfg.ext rfl rfl ?_ ?_ rfl
  · exact congrArg (fun c : Cfg K Bool (M i).State x => c.workTapes) h
  · exact congrArg (fun c : Cfg K Bool (M i).State x => c.workTapePos) h

/-- Run one clean module inside the body, forwarding exactly its output.
**Proof sketch.** Padding preserves the source run. The audited `emit_run`
then transfers every live prefix and the halting endpoint; live prefixes
always remain in that module's state summand, hence cannot hit the anchor. -/
private lemma satHost_call (M : Fin 6 → FinTM Bool) (K : ℕ) (hk : ∀ i, (M i).k ≤ K)
    (i : Fin 6) (hp : 0 < (M i).k) (x arg result out pre : List Bool)
    (q : (M i).State) (t : ℕ)
    (hg : ∀ v < t, ¬((M i).tm.runFrom
      (Cfg.ofWords (input := x) (M i).tm.q₀ (stateWord (M i).k arg)) v).Halted)
    (he : (M i).tm.runFrom
      (Cfg.ofWords (input := x) (M i).tm.q₀ (stateWord (M i).k arg)) t =
      {Cfg.ofWords q (stateWord (M i).k result) with state := none, output := out}) :
    (∀ v < t, ((satHostTM M K hk).tm.runFrom
      {Cfg.ofWords (input := x) (satHostEntry M i) (stateWord K arg) with output := pre} v).state
        ≠ some (.inl ())) ∧
    (satHostTM M K hk).tm.runFrom
      {Cfg.ofWords (input := x) (satHostEntry M i) (stateWord K arg) with output := pre} t =
      {Cfg.ofWords (satHostRet M i) (stateWord K result) with output := pre ++ out} := by
  let c := Cfg.ofWords (input := x) (M i).tm.q₀ (stateWord (M i).k arg)
  let emb : (M i).State → SatHostState M := fun s => .inr ⟨i, s⟩
  have hinit : emitCfg emb (satHostRet M i) pre (satPadCfg (K := K) c) =
      {Cfg.ofWords (input := x) (satHostEntry M i) (stateWord K arg) with output := pre} := by
    simpa [emb, c, satHostEntry] using
      satHost_seam M K i hp x arg pre [] (M i).tm.q₀ (some (M i).tm.q₀)
  have hrun (v : ℕ) (hv : v ≤ t) :
      (satHostTM M K hk).tm.runFrom
        {Cfg.ofWords (input := x) (satHostEntry M i) (stateWord K arg) with output := pre} v =
        emitCfg emb (satHostRet M i) pre (satPadCfg ((M i).tm.runFrom c v)) := by
    rw [← hinit]
    rw [emit_run (satPadTM (M i) K (hk i)).tm (satHostTM M K hk).tm emb (satHostRet M i)
      (by intros; rfl) pre _ v (by
        intro u hu
        rw [satPad_run]
        exact hg u (by omega))]
    rw [satPad_run]
  constructor
  · intro v hv
    rw [hrun v (Nat.le_of_lt hv)]
    have hl := hg v hv
    cases hs : ((M i).tm.runFrom c v).state with
    | none => exact False.elim (hl hs)
    | some s => simp [emitCfg, satPadCfg, hs, emb]
  · rw [hrun t (Nat.le_refl _), show (M i).tm.runFrom c t = _ from he]
    exact satHost_seam M K i hp x result pre out q none

/-- Joining two guarded segments preserves the first-return guard when the
intermediate seam is also outside the anchor. -/
private lemma sat_guard_add {k : ℕ} {S : Type} {x : List Bool}
    (tm : MultiTapeTM k Bool S) (anchor : S) (c d : Cfg k Bool S x) (a b : ℕ)
    (ha : ∀ v < a, (tm.runFrom c v).state ≠ some anchor)
    (he : tm.runFrom c a = d)
    (hb : ∀ v < b, (tm.runFrom d v).state ≠ some anchor) :
    ∀ v < a + b, (tm.runFrom c v).state ≠ some anchor := by
  intro v hv
  by_cases h : v < a
  · exact ha v h
  · have hva : a ≤ v := by omega
    rw [← Nat.add_sub_of_le hva, MultiTapeTM.runFrom_add, he]
    exact hb (v - a) (by omega)

/-- Uniform clean-module contract: a first halt with a prescribed replacement
word and emitted chunk, over every untouched native input. -/
private def SatClean (M : FinTM Bool) (result emit : List Bool → List Bool) (B : ℕ → ℕ) : Prop :=
  0 < M.k ∧ ∀ x arg : List Bool, ∃ t, 0 < t ∧ t ≤ B arg.length ∧
    (∀ v < t, ¬(M.tm.runFrom (Cfg.ofWords (input := x) M.tm.q₀ (stateWord M.k arg)) v).Halted) ∧
    M.tm.runFrom (Cfg.ofWords (input := x) M.tm.q₀ (stateWord M.k arg)) t =
      {Cfg.ofWords M.tm.q₀ (stateWord M.k (result arg)) with state := none, output := emit arg}

/-- Turn a clean-call bridge contract into the uniform first-halting form.
**Proof sketch.** The release wrapper stops one step after the positive exit;
minimal-halt cutting retains its entire clean configuration. -/
private lemma satClean_stop (C : FinTM Bool) (entry exit : C.State)
    (result emit : List Bool → List Bool) (B : ℕ → ℕ) (hk : 0 < C.k)
    (h : ∀ x arg : List Bool, ∃ t ≤ B arg.length, 0 < t ∧
      (∀ v, 0 < v → v < t → (C.tm.runFrom
        (Cfg.ofWords (input := x) entry (stateWord C.k arg)) v).state ≠ some exit) ∧
      C.tm.runFrom (Cfg.ofWords (input := x) entry (stateWord C.k arg)) t =
        {Cfg.ofWords exit (stateWord C.k (result arg)) with output := emit arg}) :
    SatClean (satStopTM C entry exit) result emit (fun n => B n + 1) := by
  refine ⟨hk, fun x arg => ?_⟩
  obtain ⟨t, hb, ht, hg, he⟩ := h x arg
  have hs := satStop_clean C entry exit x arg (result arg) (emit arg) t ht hg he
  obtain ⟨u, hu, hut, hguard, hend⟩ := sat_call_first_halt (satStopTM C entry exit).tm
    (Cfg.ofWords (input := x) (false, entry) (stateWord C.k arg)) (t + 1)
    (by simp [Cfg.ofWords]) (by rw [hs])
  refine ⟨u, hu, by dsimp only; omega, hguard, ?_⟩
  simpa only [satStopTM, Cfg.ofWords] using hend.trans hs

/-- The bridge overhead is bounded by one monomial of degree one higher.
**Proof sketch.** Output length is bounded by source time; `n+1` and both
source-time terms fit the larger power. The last unit pays for stopping. -/
private lemma sat_bridge_bound (c A d n len : ℕ) (hlen : len ≤ A * (n + 1) ^ d) :
    c * (A * (n + 1) ^ d + n + len + 1) + 1 ≤
      (c * (2 * A + 1) + 1) * (n + 1) ^ (d + 1) := by
  have hd := Nat.mul_le_mul_left A
    (Nat.pow_le_pow_right (Nat.succ_pos n) (show d ≤ d + 1 by omega))
  simp only [Nat.succ_eq_add_one] at hd
  have hn : n + 1 ≤ (n + 1) ^ (d + 1) := by
    simpa using Nat.pow_le_pow_right (Nat.succ_pos n) (show 1 ≤ d + 1 by omega)
  have h1 : 1 ≤ (n + 1) ^ (d + 1) := by omega
  calc
    _ ≤ c * ((2 * A + 1) * (n + 1) ^ (d + 1)) + 1 := by
      apply Nat.add_le_add_right
      apply Nat.mul_le_mul_left
      simp only [Nat.add_mul, Nat.one_mul, Nat.mul_assoc, two_mul]
      omega
    _ ≤ c * ((2 * A + 1) * (n + 1) ^ (d + 1)) + (n + 1) ^ (d + 1) := Nat.add_le_add_left h1 _
    _ = _ := by ring

/-- Every polynomial word computation has a clean first-halting install
module with a polynomial budget on the argument length. -/
private lemma satClean_install {f : List Bool → List Bool} (hf : PolyTimeComputable f) :
    ∃ M A d, SatClean M f (fun _ => []) (fun n => A * (n + 1) ^ d) := by
  obtain ⟨F, A, d, hF⟩ := hf
  obtain ⟨C, entry, exit, c, hk, hc⟩ := FinTM.exists_installCallTM F f _ hF
  -- The bridge's result length depends on the word, so enlarge it pointwise
  -- to source time before putting it in the uniform argument-length budget.
  have hlen (arg : List Bool) : (f arg).length ≤ A * (arg.length + 1) ^ d := by
    have ho := ((FinTM.computesInTime_iff _ _ _ _).mp (hF arg)).2
    simpa only [ho] using F.tm.output_length_le arg (A * (arg.length + 1) ^ d)
  have hstop := satClean_stop C entry exit f (fun _ => [])
    (fun n => c * (A * (n + 1) ^ d + n + A * (n + 1) ^ d + 1)) hk (by
      intro x arg
      obtain ⟨t, ht, hp, hg, he⟩ := hc x arg
      refine ⟨t, ht.trans (Nat.mul_le_mul_left c (by have := hlen arg; omega)), hp, hg, ?_⟩
      exact he)
  refine ⟨satStopTM C entry exit, c * (2 * A + 1) + 1, d + 1, hk, fun x arg => ?_⟩
  obtain ⟨t, hp, ht, hg, he⟩ := hstop.2 x arg
  exact ⟨t, hp, ht.trans (sat_bridge_bound c A d arg.length _ (Nat.le_refl _)), hg, he⟩

/-- The emit-mode counterpart preserves the argument and forwards the exact
computed chunk. Its polynomial budget includes cleanup and the final halt. -/
private lemma satClean_emit {f : List Bool → List Bool} (hf : PolyTimeComputable f) :
    ∃ M A d, SatClean M id f (fun n => A * (n + 1) ^ d) := by
  obtain ⟨F, A, d, hF⟩ := hf
  obtain ⟨C, entry, exit, c, hk, hc⟩ := FinTM.exists_emitCallTM F f _ hF
  have hlen (arg : List Bool) : (f arg).length ≤ A * (arg.length + 1) ^ d := by
    have ho := ((FinTM.computesInTime_iff _ _ _ _).mp (hF arg)).2
    simpa only [ho] using F.tm.output_length_le arg (A * (arg.length + 1) ^ d)
  have hstop := satClean_stop C entry exit id f
    (fun n => c * (A * (n + 1) ^ d + n + A * (n + 1) ^ d + 1)) hk (by
      intro x arg
      obtain ⟨t, ht, hp, hg, he⟩ := hc x arg
      exact ⟨t, ht.trans (Nat.mul_le_mul_left c (by have := hlen arg; omega)), hp, hg, he⟩)
  refine ⟨satStopTM C entry exit, c * (2 * A + 1) + 1, d + 1, hk, fun x arg => ?_⟩
  obtain ⟨t, hp, ht, hg, he⟩ := hstop.2 x arg
  exact ⟨t, hp, ht.trans (sat_bridge_bound c A d arg.length _ (Nat.le_refl _)), hg, he⟩

/-- Pairing length, used to charge every request to the original input. -/
private lemma satPair_length (u v : List Bool) :
    (pairEncode u v).length = 2 * u.length + v.length + 2 := by
  simp [pairEncode, List.length_flatMap, Nat.mul_comm] <;> omega

/-- Every polynomial on a linearly bounded request fits the common power. -/
private lemma sat_request_budget (A d D n m : ℕ) (hd : d ≤ D)
    (hm : m + 1 ≤ 32 * (n + 1)) :
    A * (m + 1) ^ d ≤ A * (32 * (n + 1)) ^ D := by
  apply Nat.mul_le_mul_left
  exact (Nat.pow_le_pow_left hm d).trans
    (Nat.pow_le_pow_right (by omega) hd)

/-- Specialize a clean module to one call site in the finite host. -/
private lemma satHost_clean (M : Fin 6 → FinTM Bool) (K : ℕ) (hk : ∀ i, (M i).k ≤ K)
    (i : Fin 6) (f g : List Bool → List Bool) (B : ℕ → ℕ)
    (h : SatClean (M i) f g B) (x arg pre : List Bool) :
    ∃ t, 0 < t ∧ t ≤ B arg.length ∧
      (∀ v < t, ((satHostTM M K hk).tm.runFrom
        {Cfg.ofWords (input := x) (satHostEntry M i) (stateWord K arg) with output := pre} v).state
          ≠ some (.inl ())) ∧
      (satHostTM M K hk).tm.runFrom
        {Cfg.ofWords (input := x) (satHostEntry M i) (stateWord K arg) with output := pre} t =
        {Cfg.ofWords (satHostRet M i) (stateWord K (f arg)) with output := pre ++ g arg} := by
  obtain ⟨t, hp, ht, hg, he⟩ := h.2 x arg
  obtain ⟨hguard, hend⟩ := satHost_call M K hk i h.1 x arg (f arg) (g arg) pre (M i).tm.q₀ t hg he
  exact ⟨t, hp, ht, hguard, hend⟩

/-- The full normalized emitter is polynomial-time computable.
**Proof sketch.** Build four clean modules for startup, request packing, chunk
emission, and next-state installation. The marker-free appender supplies the
native input at startup and in every round. Their finite tagged host has one
anchor, a validated startup seam, and positive first-return rounds with only
the canonical state word left on tape zero. Request sizes are linear in the
original input, so one common polynomial bounds all calls and cleanup. Invoke
`exists_emitLoopTM` with `R n = n`, then use the exact chunk-table identity. -/
private lemma satReduction_poly : PolyTimeComputable satReduction := by
  obtain ⟨S, aS, dS, hS⟩ := satClean_install satStreamStart_poly
  obtain ⟨P, aP, dP, hP⟩ := satClean_install
    (sat_pt_pair polyTimeComputable_id (sat_pt_const []))
  obtain ⟨E, aE, dE, hE⟩ := satClean_emit satReqEmit_poly
  obtain ⟨I, aI, dI, hI⟩ := satClean_install satReqStep_poly
  obtain ⟨F, aF, hF⟩ := FinTM.computesFunInTime_lengthBits
  let M : Fin 6 → FinTM Bool := fun i => match i.val with
    | 0 => satAppendTM | 1 => S | 2 => P | 3 => satAppendTM | 4 => E | _ => I
  let K := 1 + S.k + P.k + E.k + I.k
  have hk : ∀ i, (M i).k ≤ K := by
    intro i; fin_cases i <;> simp [M, K, satAppendTM] <;> omega
  let H := satHostTM M K hk
  let anchor : H.State := .inl ()
  let D := dS + dP + dE + dI + 1
  let A := aS + aP + aE + aI + aF + 200
  let pow (n : ℕ) := (32 * (n + 1)) ^ D
  let T (n : ℕ) := A * pow n
  have hpow (n : ℕ) : n + 1 ≤ pow n := by
    have h := Nat.pow_le_pow_right (show 0 < 32 * (n + 1) by omega) (show 1 ≤ D by dsimp [D]; omega)
    simp only [Nat.pow_one] at h
    exact (by omega : n + 1 ≤ 32 * (n + 1)).trans h
  have hret0 : satHostRet M 0 = satHostEntry M 1 := rfl
  have hret1 : satHostRet M 1 = anchor := rfl
  have hret2 : satHostRet M 2 = satHostEntry M 3 := rfl
  have hret3 : satHostRet M 3 = satHostEntry M 4 := rfl
  have hret4 : satHostRet M 4 = satHostEntry M 5 := rfl
  have hret5 : satHostRet M 5 = anchor := rfl
  have hstart : ∀ x : List Bool, ∃ t ≤ T x.length,
      (∀ v < t, (H.tm.runFrom (H.tm.initCfg x) v).state ≠ some anchor) ∧
      H.tm.runFrom (H.tm.initCfg x) t =
        Cfg.ofWords anchor (stateWord H.k (satStreamWord (satStreamStart x))) := by
    intro x
    obtain ⟨ta, hapos, hat, hag, hae⟩ := satAppend_clean x []
    have hac := satHost_call M K hk 0 (by simp [M, satAppendTM]) x [] x [] []
      (0 : Fin 5) ta hag (by simpa using hae)
    obtain ⟨haGuard, haEnd⟩ := hac
    have hi : H.tm.initCfg x = Cfg.ofWords (satHostEntry M 0) (stateWord K []) := by
      refine Cfg.ext rfl rfl ?_ rfl rfl
      funext i z; simp [MultiTapeTM.initCfg, Cfg.init, Cfg.ofWords, stateWord, FinTM.bufferTape]
    change H.tm.runFrom (Cfg.ofWords (input := x) (satHostEntry M 0) (stateWord K [])) ta =
      Cfg.ofWords (satHostRet M 0) (stateWord K x) at haEnd
    rw [hret0] at haEnd
    obtain ⟨ts, hspos, hst, hsGuard, hsEnd⟩ := satHost_clean M K hk 1
      (fun x => satStreamWord (satStreamStart x)) (fun _ => [])
      (fun n => aS * (n + 1) ^ dS) (by simpa [M] using hS) x x []
    change H.tm.runFrom (Cfg.ofWords (input := x) (satHostEntry M 1) (stateWord K x)) ts =
      Cfg.ofWords (satHostRet M 1) (stateWord K (satStreamWord (satStreamStart x))) at hsEnd
    rw [hret1] at hsEnd
    have hsB := sat_request_budget aS dS D x.length x.length (by dsimp [D]; omega) (by omega)
    have hp := hpow x.length
    refine ⟨ta + ts, ?_, ?_, ?_⟩
    · dsimp only [T, A, pow]
      simp only [List.length_nil] at hat
      simp only [Nat.add_mul, Nat.mul_one]
      dsimp only [pow] at hp
      omega
    · rw [hi]
      exact sat_guard_add H.tm anchor _ _ ta ts haGuard haEnd hsGuard
    · rw [hi, MultiTapeTM.runFrom_add, haEnd, hsEnd]
      rfl
  have hround : ∀ x w : List Bool, satStreamInv x w → ∃ t, 0 < t ∧ t ≤ T x.length ∧
      (∀ v, 0 < v → v < t → (H.tm.runFrom
        (Cfg.ofWords (input := x) anchor (stateWord H.k w)) v).state ≠ some anchor) ∧
      H.tm.runFrom (Cfg.ofWords (input := x) anchor (stateWord H.k w)) t =
        {Cfg.ofWords anchor (stateWord H.k (satStreamStep x w)) with output := satStreamEmit x w} := by
    intro x w hw
    obtain ⟨s, rfl, hb⟩ := hw
    let w := satStreamWord s
    let packed := pairEncode w []
    let req := pairEncode w x
    have hwlen : w.length ≤ 6 * x.length + 8 := (satStreamBound_size x s hb).2
    have hplen : packed.length = 2 * w.length + 2 := by simp [packed, satPair_length]
    have hrlen : req.length = 2 * w.length + x.length + 2 := satPair_length w x
    have hpa : packed ++ x = req := by simp [packed, req, pairEncode, List.append_assoc]
    have hstep : satReqStep req = satStreamStep x w := by
      simpa [req, w, satStreamStep, satStreamRead_word] using (satReq_round x s).1
    have hemit : satReqEmit req = satStreamEmit x w := by
      simpa [req, w, satStreamEmit, satStreamRead_word] using (satReq_round x s).2
    have hdispatch : H.tm.step (Cfg.ofWords (input := x) anchor (stateWord K w)) =
        Cfg.ofWords (satHostEntry M 2) (stateWord K w) := by
      change (FinTM.controlAction 0 (some (satHostEntry M 2))).apply _ = _
      simp [FinTM.controlAction, Action.apply, Cfg.ofWords]
      exact ⟨rfl, rfl⟩
    obtain ⟨tp, hppos, hpt, hpGuard, hpEnd⟩ := satHost_clean M K hk 2
      (fun w => pairEncode w []) (fun _ => []) (fun n => aP * (n + 1) ^ dP)
      (by simpa [M, id_eq] using hP) x w []
    change H.tm.runFrom (Cfg.ofWords (input := x) (satHostEntry M 2) (stateWord K w)) tp =
      Cfg.ofWords (satHostRet M 2) (stateWord K packed) at hpEnd
    rw [hret2] at hpEnd
    obtain ⟨ta, hapos, hat, hag, hae⟩ := satAppend_clean x packed
    obtain ⟨haGuard, haEnd⟩ := satHost_call M K hk 3 (by simp [M, satAppendTM])
      x packed req [] [] (0 : Fin 5) ta hag (by simpa [hpa] using hae)
    change H.tm.runFrom (Cfg.ofWords (input := x) (satHostEntry M 3) (stateWord K packed)) ta =
      Cfg.ofWords (satHostRet M 3) (stateWord K req) at haEnd
    rw [hret3] at haEnd
    obtain ⟨te, hepos, het, heGuard, heEnd⟩ := satHost_clean M K hk 4 id satReqEmit
      (fun n => aE * (n + 1) ^ dE) (by simpa [M] using hE) x req []
    change H.tm.runFrom (Cfg.ofWords (input := x) (satHostEntry M 4) (stateWord K req)) te =
      {Cfg.ofWords (satHostRet M 4) (stateWord K req) with output := satReqEmit req} at heEnd
    rw [hret4] at heEnd
    obtain ⟨ti, hipos, hit, hiGuard, hiEnd⟩ := satHost_clean M K hk 5 satReqStep (fun _ => [])
      (fun n => aI * (n + 1) ^ dI) (by simpa [M] using hI) x req (satReqEmit req)
    change H.tm.runFrom
      {Cfg.ofWords (input := x) (satHostEntry M 5) (stateWord K req) with output := satReqEmit req} ti =
      {Cfg.ofWords (satHostRet M 5) (stateWord K (satReqStep req)) with output := satReqEmit req ++ []} at hiEnd
    rw [List.append_nil, hret5] at hiEnd
    have hpB := sat_request_budget aP dP D x.length w.length (by dsimp [D]; omega) (by omega)
    have heB := sat_request_budget aE dE D x.length req.length (by dsimp [D]; omega) (by omega)
    have hiB := sat_request_budget aI dI D x.length req.length (by dsimp [D]; omega) (by omega)
    have hpow' := hpow x.length
    have hpAE : H.tm.runFrom (Cfg.ofWords (input := x) (satHostEntry M 2) (stateWord K w))
        (tp + ta) = Cfg.ofWords (satHostEntry M 4) (stateWord K req) := by
      rw [MultiTapeTM.runFrom_add, hpEnd, haEnd]
    have hpAguard := sat_guard_add H.tm anchor _ _ tp ta hpGuard hpEnd haGuard
    have hpAEguard := sat_guard_add H.tm anchor _ _ (tp + ta) te hpAguard hpAE heGuard
    have hpAEE : H.tm.runFrom (Cfg.ofWords (input := x) (satHostEntry M 2) (stateWord K w))
        (tp + ta + te) = {Cfg.ofWords (satHostEntry M 5) (stateWord K req) with output := satReqEmit req} := by
      rw [MultiTapeTM.runFrom_add, hpAE, heEnd]
    have hguard := sat_guard_add H.tm anchor _ _ (tp + ta + te) ti hpAEguard hpAEE hiGuard
    refine ⟨(tp + ta + te + ti) + 1, by omega, ?_, ?_, ?_⟩
    · dsimp only [T, A, pow]
      simp only [Nat.add_mul]
      dsimp only [pow] at hpow'
      omega
    · intro v hv hvt
      have hvform : v = (v - 1) + 1 := by omega
      change (H.tm.runFrom (Cfg.ofWords (input := x) anchor (stateWord K w)) v).state ≠ some anchor
      rw [hvform, MultiTapeTM.runFrom_succ_eq_step, hdispatch]
      exact hguard (v - 1) (by omega)
    · change H.tm.runFrom (Cfg.ofWords (input := x) anchor (stateWord K w))
        ((tp + ta + te + ti) + 1) = _
      rw [MultiTapeTM.runFrom_succ_eq_step, hdispatch, MultiTapeTM.runFrom_add, hpAEE, hiEnd]
      rw [hstep, hemit]
      rfl
  have hFuel : F.ComputesFunInTime (fun x => Nat.bits x.length) T := by
    intro x
    apply (hF x).mono
    have hp := Nat.mul_le_mul_left aF (hpow x.length)
    dsimp only [T, A]
    simp only [Nat.add_mul]
    omega
  obtain ⟨L, c, hL⟩ := FinTM.exists_emitLoopTM H F anchor satStreamInv satStreamStep satStreamEmit
    (fun x => satStreamWord (satStreamStart x)) id T hFuel satStreamInv_start satStreamInv_step hstart hround
  refine ⟨L, 2 * c * (A * 32 ^ D + 1), D + 1, fun x => ?_⟩
  have hcalc : c * (T x.length + 1) * (x.length + 2) ≤
      (2 * c * (A * 32 ^ D + 1)) * (x.length + 1) ^ (D + 1) := by
    have h1 : 1 ≤ (x.length + 1) ^ D := Nat.one_le_pow _ _ (by omega)
    have hb : T x.length + 1 ≤ (A * 32 ^ D + 1) * (x.length + 1) ^ D := by
      dsimp only [T, pow]
      simp only [Nat.mul_pow, Nat.add_mul, Nat.one_mul, ← Nat.mul_assoc]
      omega
    calc
      _ ≤ (c * ((A * 32 ^ D + 1) * (x.length + 1) ^ D)) * (2 * (x.length + 1)) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left c hb) (by omega)
      _ = _ := by rw [Nat.pow_succ]; ring
  have hout := (hL x).mono hcalc
  simpa only [id_eq, satStream_output_identity] using hout

/-- **`SAT ≤ₚ 3SAT`** [AB09, Lemma 2.14]: clause splitting with fresh
variables.

**Proof sketch.** The formula-level transform `t : CNF ℕ → CNF ℕ` maps each
clause of width `> 3` to a chain: `C = ℓ₁ ∨ ℓ₂ ∨ rest` becomes
`(ℓ₁ ∨ ℓ₂ ∨ z) ∧ t(¬z ∨ rest)` with `z` a fresh variable, recursively until
width `≤ 3` ([AB09, §2.3.5]); clauses of width `≤ 3` pass through. Fresh
variables are allocated from `φ.numVars` upward by a running counter, so
freshness is by construction (indices `≥ numVars` are unmentioned —
`Complexity.eval_congr_of_lt_numVars`'s bound). **Equisatisfiability**, the
mathematical content, by induction on the splitting: forward, a satisfying
assignment extends to the fresh variables by giving each `z` the value "the
tail `rest` is satisfied" (if `ℓ₁ ∨ ℓ₂` already holds, `z := false` keeps the
second clause on its `¬z` disjunct — [AB09]'s case analysis); backward, a
satisfying assignment of the image restricted to the original variables
satisfies `C`, since from `(ℓ₁ ∨ ℓ₂ ∨ z)` and inductively `¬z ∨ rest` either
some original literal holds or the chain walks to one. Width and size: every
output clause has width `≤ 3`, and the output has at most `|C| - 2` chain
links per clause — total size linear in the input size, fresh indices at most
`numVars + Σ widths`. **The string-level reduction** is
`f = Std.Sat.CNF.serialize ∘ t ∘ Std.Sat.CNF.decode`, with
`Complexity.PolyTimeComputable f` by the named machine obligations: the parsing
machine (shared with `Complexity.SAT_mem_NP`), the streaming transform (a
clause buffer, a width counter, and the fresh-variable counter whose unary
serialization stays linear in the output position), and the serializer;
output length polynomial in `|x|`. **Correctness for every string**:
well-formed `x` by `Std.Sat.CNF.decode_serialize` and equisatisfiability
(width of `t φ` is `≤ 3` by construction); non-well-formed `x` decodes to the
fallback `[]`, which `t` fixes, so `f x = Std.Sat.CNF.serialize []` — and both
sides of `x ∈ SAT ↔ f x ∈ SAT3` are true (the fallback and the empty formula
are satisfiable and 3CNF). Conclude with the definition
`Complexity.PolyTimeReducible`. -/
theorem SAT_reducible_SAT3 : SAT ≤ₚ SAT3 := by
  exact ⟨satReduction, satReduction_poly, satReduction_correct⟩

end Complexity
