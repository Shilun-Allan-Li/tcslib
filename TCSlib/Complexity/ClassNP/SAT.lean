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
The last work head moves only on the first of the two physical transitions. -/
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
cost is linear in the native paired-input length. -/
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
single-bit decision. All three budgets fit their maximum degree. -/
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
The conclusion holds also on failed splits and failed parses. -/
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
and runs the evaluation pass only after width success. -/
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
  sorry

end Complexity
