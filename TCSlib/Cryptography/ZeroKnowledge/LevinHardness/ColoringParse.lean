/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.ZeroKnowledge.LevinHardness.ColoringGraph
import TCSlib.Cryptography.ZeroKnowledge.LevinHardness.Bridge

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Parsing tests of the 3SAT → 3COL instance map

The two string tests of the instance map `colorInst` (`LevinHardness/ColoringGraph.lean`) of
the Levin reduction `3SAT → 3COL` ([AB09, §2.3]; the course reduction
`Complexity/NPReductions/ThreeSATToColoring.lean`, CS 294-268, UC Berkeley, Spring 2026) are
polynomial-time, so the instance map is.

The serialization `Std.Sat.CNF.serialize` is read only through the readers of
`LevinHardness/Bridge.lean`. A position `p` of a well-formed string `s` is a *clause boundary*
when the grammar automaton `Std.Sat.CNF.syntaxStep` is back in its formula state `0` after
`s.take p`; every such prefix is the serialization of a list of clauses (`exists_recs_of_foldl`).

* `memS s c` holds iff `s` is well-formed and, at some clause boundary, `s` continues with the
  record `1 :: serializeClause C'` of one of the at most three clauses `C'` with clause code `c`
  (`candClause`, `memS_eq`).
* `goodS s` holds iff `s` is not well-formed or a finite automaton counting the literals of each
  clause up to four (`widthStep`) never sees an empty or over-long clause (`goodS_eq`).

## Main definitions

* `litOfCode`, `candClause`, `candValid` — the clauses with a given clause code.
* `clauseRec`, `boundary`, `memAlg` — clause records, clause boundaries, the string test of `memS`.
* `widthStep` — the width automaton.

## Main results

* `var_lt_length_of_mem_decode`, `clauseSat_of_memS` — variables of `CNF.decode s` are `< |s|`;
  the unconditional bridge to the colouring witness.
* `polyTimeComputable_foldl_accept` — a finite automaton's verdict is polynomial-time.
* `memS_eq`, `goodS_eq` — the string forms of the two tests.
* `polyTimeComputable_memS`, `polyTimeComputable_goodS`, `polyTimeComputable_colorInst`.

## References

* CS 294-268 course material (UC Berkeley, Spring 2026, V. Guruswami), the 3SAT → 3-colouring
  reduction as formalized in `Complexity/NPReductions/ThreeSATToColoring.lean`.
* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Cambridge
  University Press, 2009. (§2.3.)
-/

namespace TCSlib.Cryptography.LevinHardness

open Std.Sat Complexity

/-! ### The variable bound -/

/-- Glue: a member of a list of naturals is at most its `foldr max 0`. -/
private theorem le_foldr_max_zero {n : ℕ} {l : List ℕ} (h : n ∈ l) : n ≤ l.foldr max 0 := by
  induction l with
  | nil => cases h
  | cons m l ih =>
    rcases List.mem_cons.1 h with rfl | h
    · exact le_max_left _ _
    · exact (ih h).trans (le_max_right _ _)

/-- **Variables of a decoded formula are below the string length**: for `C ∈ CNF.decode s` and
`ℓ ∈ C`, `ℓ.1 < |s|` (`Bridge.numVars_eq`, `CNF.numVars_decode_le`). Glue. -/
theorem var_lt_length_of_mem_decode {s : List Bool} {C : CNF.Clause ℕ}
    (hC : C ∈ CNF.decode s) {ℓ : Literal ℕ} (hℓ : ℓ ∈ C) : ℓ.1 < s.length := by
  have h1 : ℓ.1 + 1 ≤ (CNF.decode s).numVars := by
    rw [Bridge.numVars_eq]
    exact le_foldr_max_zero (List.mem_flatMap.2 ⟨C, hC, List.mem_map.2 ⟨ℓ, hℓ, rfl⟩⟩)
  have := CNF.numVars_decode_le s
  omega

/-- **A satisfying assignment satisfies every member code**: if
`(CNF.decode s).eval val = true` and `memS s c = true`, then `clauseSat |s| val c = true`
(`clauseSat_of_memS_of_lt` with `var_lt_length_of_mem_decode`). Glue. -/
theorem clauseSat_of_memS {s : List Bool} {val : ℕ → Bool} {c : ℕ}
    (heval : (CNF.decode s).eval val = true) (hm : memS s c = true) :
    clauseSat s.length val c = true :=
  clauseSat_of_memS_of_lt (fun _ hC _ hℓ => var_lt_length_of_mem_decode hC hℓ) heval hm

/-! ### Finite automata in polynomial time -/

/-- Glue: the last output of the verdict transducer is the verdict on the whole word. -/
private theorem getLastD_transduce_accept {σ : Type} (δ : σ → Bool → σ) (acc : σ → Bool)
    (x : List Bool) (q : σ) (d : Bool) :
    (transduce δ (fun q b => some (acc (δ q b))) q x).getLastD d =
      if x = [] then d else acc (x.foldl δ q) := by
  induction x generalizing q d with
  | nil => rw [transduce_nil]; rfl
  | cons b l ih =>
    rw [transduce_cons, Option.toList_some, List.singleton_append, List.getLastD_cons, ih]
    cases l <;> simp

/-- **The verdict of a finite automaton is polynomial-time**: for a finite state type `σ`, a
transition `δ`, a start state `q₀` and an acceptance test `acc`, the map
`x ↦ [acc (x.foldl δ q₀)]` is polynomial-time computable.

**Proof sketch.** The transducer emitting `acc (δ q b)` after every bit
(`polyTimeComputable_transduce`) ends with the verdict on nonempty words
(`getLastD_transduce_accept`), read by `BinArith.polyTimeComputable_lastBit`; the empty word is
split off with `polyTimeComputable_isNil` and `polyTimeComputable_ite`. -/
theorem polyTimeComputable_foldl_accept {σ : Type} [Fintype σ] [DecidableEq σ]
    (δ : σ → Bool → σ) (q₀ : σ) (acc : σ → Bool) :
    PolyTimeComputable fun x => [acc (x.foldl δ q₀)] := by
  have ht := BinArith.polyTimeComputable_lastBit.comp'
    (polyTimeComputable_transduce δ (fun q b => some (acc (δ q b))) q₀)
  refine (polyTimeComputable_ite polyTimeComputable_isNil (polyTimeComputable_const [acc q₀])
    ht).congr fun x => ?_
  by_cases hx : x = []
  · subst hx; simp
  · simp only [hx, decide_false, Bool.false_eq_true, ↓reduceIte, getLastD_transduce_accept]

/-- **The syntax pass is polynomial-time**: `x ↦ [CNF.syntaxOK x]` (`Bridge.syntaxOK_eq`,
`polyTimeComputable_foldl_accept`). -/
theorem polyTimeComputable_syntaxOK : PolyTimeComputable fun x => [CNF.syntaxOK x] :=
  (polyTimeComputable_foldl_accept CNF.syntaxStep 0 fun q => decide (q = 4)).congr fun x => by
    rw [Bridge.syntaxOK_eq]

/-! ### Clause records and clause boundaries -/

/-- **The record of a clause** in a serialized formula: `clauseRec C = 1 :: serializeClause C`. -/
def clauseRec (C : CNF.Clause ℕ) : List Bool := true :: CNF.serializeClause C

/-- The defining equation of `clauseRec`. -/
theorem clauseRec_eq (C : CNF.Clause ℕ) : clauseRec C = true :: CNF.serializeClause C := rfl

/-- Glue: a serialized formula is its clause records followed by `0`. -/
theorem serialize_eq_recs (φ : CNF ℕ) : CNF.serialize φ = φ.flatMap clauseRec ++ [false] := by
  rw [Bridge.serialize_eq]; rfl

/-- Glue: a well-formed string is the serialization of its decoding. -/
theorem eq_serialize_decode {s : List Bool} (h : CNF.syntaxOK s = true) :
    s = CNF.serialize (CNF.decode s) := by
  rw [CNF.syntaxOK_spec] at h
  obtain ⟨φ, hφ⟩ := Option.isSome_iff_exists.1 h
  rw [Bridge.decode_eq, hφ, Option.getD_some]
  exact CNF.parse_repr hφ

/-- Glue: serializations are well-formed. -/
theorem syntaxOK_serialize (φ : CNF ℕ) : CNF.syntaxOK (CNF.serialize φ) = true := by
  rw [CNF.syntaxOK_spec, CNF.parse_serialize]; rfl

/-- Glue: the serialization is injective (`CNF.parse_serialize`). -/
theorem serialize_injective {φ ψ : CNF ℕ} (h : CNF.serialize φ = CNF.serialize ψ) : φ = ψ := by
  have := CNF.parse_serialize φ
  rw [h, CNF.parse_serialize] at this
  exact (Option.some.inj this).symm

/-- Glue: the automaton accepts exactly when its run ends in the exact-end state `4`. -/
private theorem foldl_eq_four {x : List Bool} :
    x.foldl CNF.syntaxStep 0 = 4 ↔ CNF.syntaxOK x = true := by
  rw [Bridge.syntaxOK_eq, decide_eq_true_iff]

/-- Glue: reading `0` leads to the exact-end state only from the formula state. -/
private theorem syntaxStep_false_eq_four {q : Fin 6} (h : CNF.syntaxStep q false = 4) : q = 0 := by
  rw [Bridge.syntaxStep_eq] at h
  fin_cases q <;> simp_all

/-- **A clause record returns the automaton to the formula state**:
`(clauseRec C).foldl syntaxStep 0 = 0`. Glue. -/
theorem foldl_clauseRec (C : CNF.Clause ℕ) : (clauseRec C).foldl CNF.syntaxStep 0 = 0 := by
  have h := foldl_eq_four.2 (syntaxOK_serialize [C])
  rw [serialize_eq_recs, List.flatMap_singleton, List.foldl_append, List.foldl_cons,
    List.foldl_nil] at h
  exact syntaxStep_false_eq_four h

/-- Glue: a list of clause records returns the automaton to the formula state. -/
theorem foldl_recs (χ : CNF ℕ) : (χ.flatMap clauseRec).foldl CNF.syntaxStep 0 = 0 := by
  induction χ with
  | nil => rfl
  | cons C χ ih => rw [List.flatMap_cons, List.foldl_append, foldl_clauseRec, ih]

/-- **Prefixes ending in the formula state are lists of clause records**: if
`t.foldl syntaxStep 0 = 0`, then `t = χ.flatMap clauseRec` for some clause list `χ`. Glue.

**Proof sketch.** `t ++ [0]` is accepted (state `0` reads `0` into `4`), so it is the
serialization of some `χ` (`eq_serialize_decode`), i.e. `χ.flatMap clauseRec ++ [0]`. -/
theorem exists_recs_of_foldl {t : List Bool} (h : t.foldl CNF.syntaxStep 0 = 0) :
    ∃ χ : CNF ℕ, t = χ.flatMap clauseRec := by
  have hok : CNF.syntaxOK (t ++ [false]) = true := by
    rw [← foldl_eq_four, List.foldl_append, h, List.foldl_cons, List.foldl_nil,
      Bridge.syntaxStep_eq]
    rfl
  refine ⟨CNF.decode (t ++ [false]), ?_⟩
  have := eq_serialize_decode hok
  rw [serialize_eq_recs] at this
  exact List.append_cancel_right this

/-- **The suffix after a clause boundary**: if `s = serialize φ` and `s.take p` ends in the
formula state, then `φ = χ ++ ψ` with `s.drop p = serialize ψ`. Glue. -/
theorem exists_split_of_boundary {φ : CNF ℕ} {p : ℕ}
    (h : ((CNF.serialize φ).take p).foldl CNF.syntaxStep 0 = 0) :
    ∃ χ ψ : CNF ℕ, φ = χ ++ ψ ∧ (CNF.serialize φ).drop p = CNF.serialize ψ := by
  obtain ⟨χ, hχ⟩ := exists_recs_of_foldl h
  have hok : CNF.syntaxOK ((CNF.serialize φ).drop p) = true := by
    have h4 := foldl_eq_four.2 (syntaxOK_serialize φ)
    rw [← List.take_append_drop p (CNF.serialize φ), List.foldl_append, h] at h4
    exact foldl_eq_four.1 h4
  obtain ⟨ψ, hψ⟩ : ∃ ψ, (CNF.serialize φ).drop p = CNF.serialize ψ :=
    ⟨_, eq_serialize_decode hok⟩
  refine ⟨χ, ψ, serialize_injective ?_, hψ⟩
  calc CNF.serialize φ = (CNF.serialize φ).take p ++ (CNF.serialize φ).drop p :=
        (List.take_append_drop p _).symm
    _ = χ.flatMap clauseRec ++ CNF.serialize ψ := by rw [hχ, hψ]
    _ = CNF.serialize (χ ++ ψ) := by
        rw [serialize_eq_recs, serialize_eq_recs, List.flatMap_append, List.append_assoc]

/-! ### Prefix-freeness of the serialization -/

/-- Glue: literal serializations are prefix-free. -/
private theorem serializeLit_append_inj {a b : Literal ℕ} {x y : List Bool}
    (h : CNF.serializeLit a ++ x = CNF.serializeLit b ++ y) : a = b ∧ x = y := by
  obtain ⟨v, β⟩ := a
  obtain ⟨w, γ⟩ := b
  rw [Bridge.serializeLit_eq, Bridge.serializeLit_eq] at h
  simp only [List.append_assoc, List.cons_append, List.nil_append] at h
  induction v generalizing w with
  | zero =>
    cases w with
    | zero => simp_all
    | succ w => simp [List.replicate_succ] at h
  | succ v ih =>
    cases w with
    | zero => simp [List.replicate_succ] at h
    | succ w =>
      obtain ⟨hab, hxy⟩ := ih w (by
        simpa only [List.replicate_succ, List.cons_append, List.cons.injEq, true_and] using h)
      simp only [Prod.mk.injEq] at hab ⊢
      exact ⟨⟨by omega, hab.2⟩, hxy⟩

/-- **Clause serializations are prefix-free**: `serializeClause C ++ x = serializeClause D ++ y`
implies `C = D` and `x = y`. Glue.

**Proof sketch.** Induction on `C`: a literal record starts with `1` and the clause terminator
is `0`, so both sides end or continue together; two literal records followed by anything agree
in their unary variable run, polarity bit and remainder (`serializeLit_eq`). -/
theorem serializeClause_append_inj {C D : CNF.Clause ℕ} {x y : List Bool}
    (h : CNF.serializeClause C ++ x = CNF.serializeClause D ++ y) : C = D ∧ x = y := by
  rw [Bridge.serializeClause_eq, Bridge.serializeClause_eq] at h
  simp only [List.append_assoc, List.singleton_append] at h
  induction C generalizing D with
  | nil =>
    cases D with
    | nil => simpa using h
    | cons b D =>
      rw [List.flatMap_cons, Bridge.serializeLit_eq] at h
      simp [List.replicate_succ] at h
  | cons a C ih =>
    cases D with
    | nil =>
      rw [List.flatMap_cons, Bridge.serializeLit_eq] at h
      simp [List.replicate_succ] at h
    | cons b D =>
      rw [List.flatMap_cons, List.flatMap_cons, List.append_assoc, List.append_assoc] at h
      obtain ⟨rfl, h'⟩ := serializeLit_append_inj h
      obtain ⟨rfl, rfl⟩ := ih h'
      exact ⟨rfl, rfl⟩

/-! ### The clauses of a clause code -/

/-- **The literal of a literal code**: `litOfCode ℓ = (ℓ / 2, decide (ℓ % 2 = 0))`. -/
def litOfCode (ℓ : ℕ) : Literal ℕ := (ℓ / 2, decide (ℓ % 2 = 0))

/-- The defining equation of `litOfCode`. -/
theorem litOfCode_eq (ℓ : ℕ) : litOfCode ℓ = (ℓ / 2, decide (ℓ % 2 = 0)) := rfl

/-- `litCode (litOfCode ℓ) = ℓ`. Glue. -/
theorem litCode_litOfCode (ℓ : ℕ) : litCode (litOfCode ℓ) = ℓ := by
  rw [litCode_eq, litOfCode_eq]
  by_cases h : ℓ % 2 = 0
  · simp only [h, decide_true, ↓reduceIte, add_zero]; omega
  · simp only [h, decide_false, Bool.false_eq_true, ↓reduceIte]; omega

/-- `litOfCode (litCode a) = a`. Glue. -/
theorem litOfCode_litCode (a : Literal ℕ) : litOfCode (litCode a) = a := by
  obtain ⟨v, β⟩ := a
  rw [litCode_eq, litOfCode_eq]
  cases β
  · simp only [Bool.false_eq_true, ↓reduceIte, Prod.mk.injEq, decide_eq_false_iff_not]; omega
  · simp only [↓reduceIte, add_zero, Prod.mk.injEq, decide_eq_true_eq]; omega

/-- **The candidate clauses of a clause code** `c` for `K` variables: with the literals
`Lᵢ = litOfCode (clauseLit K c i)`, the clause `[L₀]` (`j = 1`), `[L₀, L₁]` (`j = 2`) and
`[L₀, L₁, L₂]` (otherwise). -/
def candClause (K c : ℕ) : ℕ → CNF.Clause ℕ
  | 1 => [litOfCode (clauseLit K c 0)]
  | 2 => [litOfCode (clauseLit K c 0), litOfCode (clauseLit K c 1)]
  | _ => [litOfCode (clauseLit K c 0), litOfCode (clauseLit K c 1), litOfCode (clauseLit K c 2)]

/-- **The validity of a candidate**: `[L₀]` needs equal digits `d₀ = d₁ = d₂`, `[L₀, L₁]` needs
`d₁ = d₂` (the widening repeats the last literal), `[L₀, L₁, L₂]` is always valid
(`dᵢ = clauseLit K c i`). -/
def candValid (K c : ℕ) : ℕ → Bool
  | 1 => decide (clauseLit K c 0 = clauseLit K c 1) && decide (clauseLit K c 1 = clauseLit K c 2)
  | 2 => decide (clauseLit K c 1 = clauseLit K c 2)
  | _ => true

/-- The case readers of `candClause`: `candClause K c 1 = [L₀]`. -/
theorem candClause_one (K c : ℕ) : candClause K c 1 = [litOfCode (clauseLit K c 0)] := rfl

/-- See `candClause_one`. -/
theorem candClause_two (K c : ℕ) :
    candClause K c 2 = [litOfCode (clauseLit K c 0), litOfCode (clauseLit K c 1)] := rfl

/-- See `candClause_one`. -/
theorem candClause_three (K c : ℕ) : candClause K c 3 =
    [litOfCode (clauseLit K c 0), litOfCode (clauseLit K c 1), litOfCode (clauseLit K c 2)] :=
  rfl

/-- The case readers of `candValid`: `candValid K c 1 = (d₀ = d₁ ∧ d₁ = d₂)`. -/
theorem candValid_one (K c : ℕ) : candValid K c 1 =
    (decide (clauseLit K c 0 = clauseLit K c 1) && decide (clauseLit K c 1 = clauseLit K c 2)) :=
  rfl

/-- See `candValid_one`: `candValid K c 2 = (d₁ = d₂)`. -/
theorem candValid_two (K c : ℕ) :
    candValid K c 2 = decide (clauseLit K c 1 = clauseLit K c 2) := rfl

/-- See `candValid_one`: `candValid K c 3 = true`. -/
theorem candValid_three (K c : ℕ) : candValid K c 3 = true := rfl

/-- **The candidates are the clauses with clause code `c`**: if every variable of `φ` is `< K`,
then `(∃ C ∈ φ, 1 ≤ |C| ≤ 3 ∧ clauseCode K C = c)` iff some valid candidate `candClause K c j`
(`j = 1, 2, 3`) belongs to `φ`. Glue.

**Proof sketch.** A valid candidate has one to three literals and, its widening repeating the
last literal, digits `clauseLit K c i`, so its code is `c` (`clauseLit_decomp`). Conversely the
digits of `clauseCode K C` are the codes of the widened literals (`clauseLit_clauseCode`), so
the candidate of length `|C|` is valid and equals `C` (`litOfCode_litCode`). -/
theorem exists_mem_clauseCode_iff {K c : ℕ} {φ : CNF ℕ} (hK : ∀ C ∈ φ, ∀ ℓ ∈ C, ℓ.1 < K) :
    (∃ C ∈ φ, 1 ≤ C.length ∧ C.length ≤ 3 ∧ clauseCode K C = c) ↔
      ∃ j ∈ [1, 2, 3], candValid K c j = true ∧ candClause K c j ∈ φ := by
  have hdec := clauseLit_decomp K c
  constructor
  · rintro ⟨C, hC, h1, h3, rfl⟩
    have hd := clauseLit_clauseCode (hK C hC) h1
    match C, h1, h3 with
    | [a], _, _ =>
      have e : ∀ i : Fin 3, clauseLit K (clauseCode K [a]) i = litCode a := fun i => by
        rw [hd, wideLit_eq]; simp
      refine ⟨1, by simp, ?_, ?_⟩
      · simp [candValid, e]
      · rw [candClause_one, e, litOfCode_litCode]; simpa using hC
    | [a, b], _, _ =>
      have e0 : clauseLit K (clauseCode K [a, b]) 0 = litCode a := by rw [hd, wideLit_eq]; simp
      have e1 : clauseLit K (clauseCode K [a, b]) 1 = litCode b := by rw [hd, wideLit_eq]; simp
      have e2 : clauseLit K (clauseCode K [a, b]) 2 = litCode b := by rw [hd, wideLit_eq]; simp
      refine ⟨2, by simp, ?_, ?_⟩
      · simp [candValid, e1, e2]
      · rw [candClause_two, e0, e1, litOfCode_litCode, litOfCode_litCode]; exact hC
    | [a, b, d], _, _ =>
      have e0 : clauseLit K (clauseCode K [a, b, d]) 0 = litCode a := by
        rw [hd, wideLit_eq]; simp
      have e1 : clauseLit K (clauseCode K [a, b, d]) 1 = litCode b := by
        rw [hd, wideLit_eq]; simp
      have e2 : clauseLit K (clauseCode K [a, b, d]) 2 = litCode d := by
        rw [hd, wideLit_eq]; simp
      refine ⟨3, by simp, rfl, ?_⟩
      rw [candClause_three, e0, e1, e2, litOfCode_litCode, litOfCode_litCode, litOfCode_litCode]
      exact hC
  · rintro ⟨j, hj, hv, hmem⟩
    refine ⟨_, hmem, ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl
    · simp only [candValid, Bool.and_eq_true, decide_eq_true_eq] at hv
      rw [← hv.2, ← hv.1] at hdec
      refine ⟨by simp [candClause_one], by simp [candClause_one], ?_⟩
      simp [clauseCode_eq, candClause_one, wideLit_eq, litCode_litOfCode]
      linarith
    · simp only [candValid, decide_eq_true_eq] at hv
      rw [← hv] at hdec
      refine ⟨by simp [candClause_two], by simp [candClause_two], ?_⟩
      simp [clauseCode_eq, candClause_two, wideLit_eq, litCode_litOfCode]
      linarith
    · refine ⟨by simp [candClause_three], by simp [candClause_three], ?_⟩
      simp [clauseCode_eq, candClause_three, wideLit_eq, litCode_litOfCode]
      linarith

/-! ### The string form of `memS` -/

/-- **A clause record at a clause boundary**: `hasRec s r` holds when, at some position
`p ≤ |s|` where the grammar automaton is in its formula state after `s.take p`, the string `s`
continues with `r`. -/
def hasRec (s r : List Bool) : Bool :=
  decide (∃ p < s.length + 1, (decide ((s.take p).foldl CNF.syntaxStep 0 = 0) &&
    decide ((s.drop p).take r.length = r)) = true)

/-- The defining equation of `hasRec`. -/
theorem hasRec_eq (s r : List Bool) :
    hasRec s r = decide (∃ p < s.length + 1, (decide ((s.take p).foldl CNF.syntaxStep 0 = 0) &&
      decide ((s.drop p).take r.length = r)) = true) := rfl

/-- **Clause records at clause boundaries are the clauses**: for a serialized formula,
`hasRec (serialize φ) (clauseRec C) = true ↔ C ∈ φ`. Glue.

**Proof sketch.** At a clause boundary `p` the formula splits as `χ ++ ψ` with the suffix
`serialize ψ` (`exists_split_of_boundary`); a record prefix of it is the record of the head
clause of `ψ` by prefix-freeness (`serializeClause_append_inj`). Conversely, for
`φ = χ ++ C :: ψ` the position `|χ.flatMap clauseRec|` is a boundary (`foldl_recs`) followed by
the record of `C`. -/
theorem hasRec_serialize_iff (φ : CNF ℕ) (C : CNF.Clause ℕ) :
    hasRec (CNF.serialize φ) (clauseRec C) = true ↔ C ∈ φ := by
  rw [hasRec_eq, decide_eq_true_iff]
  constructor
  · rintro ⟨p, -, hp⟩
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hp
    obtain ⟨χ, ψ, rfl, hψ⟩ := exists_split_of_boundary hp.1
    have hpre : clauseRec C <+: CNF.serialize ψ := by
      rw [List.prefix_iff_eq_take, ← hψ]; exact hp.2.symm
    obtain ⟨t, ht⟩ := hpre
    cases ψ with
    | nil =>
      rw [serialize_eq_recs, clauseRec_eq] at ht
      simp at ht
    | cons D ψ =>
      rw [serialize_eq_recs, List.flatMap_cons, clauseRec_eq, clauseRec_eq] at ht
      simp only [List.cons_append, List.cons.injEq, true_and, List.append_assoc] at ht
      obtain ⟨rfl, -⟩ := serializeClause_append_inj ht
      exact List.mem_append_right _ List.mem_cons_self
  · intro hC
    obtain ⟨χ, ψ, rfl⟩ := List.append_of_mem hC
    refine ⟨(χ.flatMap clauseRec).length, ?_, ?_⟩
    · rw [serialize_eq_recs, List.flatMap_append, List.length_append, List.length_append]
      omega
    · have hs : CNF.serialize (χ ++ C :: ψ) =
          χ.flatMap clauseRec ++ (clauseRec C ++ (ψ.flatMap clauseRec ++ [false])) := by
        rw [serialize_eq_recs, List.flatMap_append, List.flatMap_cons, List.append_assoc,
          List.append_assoc]
      rw [hs, List.take_left' rfl, List.drop_left' rfl, List.take_left' rfl, foldl_recs]
      simp

/-- **The string test of `memS`**: `s` is well-formed and the record of a valid candidate clause
of `c` (`candClause`, `candValid`) sits at a clause boundary of `s`. -/
def memAlg (s : List Bool) (c : ℕ) : Bool :=
  CNF.syntaxOK s &&
    (candValid s.length c 1 && hasRec s (clauseRec (candClause s.length c 1)) ||
     candValid s.length c 2 && hasRec s (clauseRec (candClause s.length c 2)) ||
     candValid s.length c 3 && hasRec s (clauseRec (candClause s.length c 3)))

/-- The defining equation of `memAlg`. -/
theorem memAlg_eq (s : List Bool) (c : ℕ) :
    memAlg s c = (CNF.syntaxOK s &&
      (candValid s.length c 1 && hasRec s (clauseRec (candClause s.length c 1)) ||
       candValid s.length c 2 && hasRec s (clauseRec (candClause s.length c 2)) ||
       candValid s.length c 3 && hasRec s (clauseRec (candClause s.length c 3)))) := rfl

/-- Glue: an ill-formed string decodes to the empty formula. -/
theorem decode_eq_nil_of_syntaxOK {s : List Bool} (h : CNF.syntaxOK s = false) :
    CNF.decode s = [] := by
  rw [CNF.syntaxOK_spec, Option.isSome_eq_false_iff, Option.isNone_iff_eq_none] at h
  rw [Bridge.decode_eq, h, Option.getD_none, Bridge.fallback_eq]

/-- **`memS` is its string test**: `memS s c = memAlg s c`.

**Proof sketch.** Ill-formed strings decode to `[]` (`decode_eq_nil_of_syntaxOK`), where both
sides fail. A well-formed `s` is `serialize (decode s)` (`eq_serialize_decode`); `memS_iff`,
the variable bound `var_lt_length_of_mem_decode`, `exists_mem_clauseCode_iff` and
`hasRec_serialize_iff` identify the two sides. -/
theorem memS_eq (s : List Bool) (c : ℕ) : memS s c = memAlg s c := by
  rw [memAlg_eq]
  cases hok : CNF.syntaxOK s with
  | false =>
    simp only [Bool.false_and]
    rw [Bool.eq_false_iff, ne_eq, memS_iff, decode_eq_nil_of_syntaxOK hok]
    simp
  | true =>
    simp only [Bool.true_and]
    apply Bool.eq_iff_iff.mpr
    rw [memS_iff, exists_mem_clauseCode_iff
      (fun C hC ℓ hℓ => var_lt_length_of_mem_decode hC hℓ)]
    have hs := eq_serialize_decode hok
    have hR : ∀ j, hasRec s (clauseRec (candClause s.length c j)) = true ↔
        candClause s.length c j ∈ CNF.decode s := fun j => by
      have h := hasRec_serialize_iff (CNF.decode s) (candClause s.length c j)
      rwa [← hs] at h
    simp only [List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp, exists_eq_left,
      Bool.or_eq_true, Bool.and_eq_true, hR, or_assoc]

/-! ### `memS` in polynomial time -/

/-- **The boundary-record test is polynomial-time**: for polynomial-time `S`, `R`, the map
`w ↦ [hasRec (S w) (R w)]` is polynomial-time.

**Proof sketch.** A bounded search (`EncodingMachines.polyTimeComputable_firstIdx`, bound
`|S w| + 1`) for a position `p` where the automaton verdict on `(S w).take p`
(`polyTimeComputable_foldl_accept` after `polyTimeComputable_takePrefixByLength`) is the formula
state and `((S w).drop p).take |R w| = R w` (`polyTimeComputable_pairDropPoly`,
`BinArith.polyTimeComputable_eqW`); success is `firstIdx < |S w| + 1`
(`EncodingMachines.firstIdx_lt_iff`). -/
theorem polyTimeComputable_hasRec {S R : List Bool → List Bool} (hS : PolyTimeComputable S)
    (hR : PolyTimeComputable R) : PolyTimeComputable fun w => [hasRec (S w) (R w)] := by
  open EncodingMachines in
  have hSv : PolyTimeComputable fun v => S (pairSndD v) := hS.comp' polyTimeComputable_pairSndD
  have hRv : PolyTimeComputable fun v => R (pairSndD v) := hR.comp' polyTimeComputable_pairSndD
  have hpair := polyTimeComputable_pairFstD.pairEncode hSv
  have htake : PolyTimeComputable fun v => (S (pairSndD v)).take (pairFstD v).length :=
    (polyTimeComputable_takePrefixByLength.comp' hpair).congr fun v => by
      rw [PrefixByLength.take_def, pairFstD_pairEncode, pairSndD_pairEncode]
  have hdrop : PolyTimeComputable fun v => (S (pairSndD v)).drop (pairFstD v).length :=
    ((polyTimeComputable_pairDropPoly .var).comp' hpair).congr fun v => by
      simp only [pairFstD_pairEncode, pairSndD_pairEncode, PolyExpr.eval_var]
  have hbd : PolyTimeComputable fun v =>
      [decide (((S (pairSndD v)).take (pairFstD v).length).foldl CNF.syntaxStep 0 = 0)] :=
    (polyTimeComputable_foldl_accept CNF.syntaxStep 0 fun q => decide (q = 0)).comp' htake
  have htake2 : PolyTimeComputable fun v =>
      ((S (pairSndD v)).drop (pairFstD v).length).take (R (pairSndD v)).length :=
    (polyTimeComputable_takePrefixByLength.comp' (hRv.pairEncode hdrop)).congr fun v => by
      rw [PrefixByLength.take_def, pairFstD_pairEncode, pairSndD_pairEncode]
  have heq : PolyTimeComputable fun v =>
      [decide (((S (pairSndD v)).drop (pairFstD v).length).take (R (pairSndD v)).length =
        R (pairSndD v))] :=
    (BinArith.polyTimeComputable_eqW.comp' (htake2.pairEncode hRv)).congr fun v => by
      rw [BinArith.eqW_pairEncode]
  have hlen : PolyTimeComputable fun w => List.replicate ((S w).length + 1) true :=
    unaryAdd_poly (unaryLength_poly hS) (unaryConst_poly 1)
  have hf := polyTimeComputable_firstIdx
    (p := fun w p => decide (((S w).take p).foldl CNF.syntaxStep 0 = 0) &&
      decide (((S w).drop p).take (R w).length = R w)) (polyTimeComputable_and hbd heq) hlen
  refine (ltTest_poly hf hlen).congr fun w => ?_
  rw [hasRec_eq]
  simp only [firstIdx_lt_iff]

/-- Glue: the serialization of the literal of a unary code is polynomial-time,
`x ↦ serializeLit (litOfCode (ℓ x)) = 1^(ℓ x / 2 + 1) ++ [0, ℓ x even]`
(`Bridge.serializeLit_eq`). -/
private theorem polyTimeComputable_serializeLit_litOfCode {ℓ : List Bool → ℕ}
    (hℓ : PolyTimeComputable fun x => List.replicate (ℓ x) true) :
    PolyTimeComputable fun x => CNF.serializeLit (litOfCode (ℓ x)) := by
  open EncodingMachines in
  refine ((unaryAdd_poly (unaryDivConst_poly hℓ 2) (unaryConst_poly 1)).append
    ((polyTimeComputable_const [false]).append
      (eqTest_poly (unaryModConst_poly hℓ 2) (unaryConst_poly 0)))).congr fun x => ?_
  rw [Bridge.serializeLit_eq, litOfCode_eq]
  rfl

/-- **`memS` is polynomial-time**: `⟨1^c, s⟩ ↦ [memS s c]`.

**Proof sketch.** `memS_eq`: the syntax pass (`polyTimeComputable_syntaxOK`), the validity
tests (`EncodingMachines.eqTest_poly` on `clauseLit_poly`) and the record tests
(`polyTimeComputable_hasRec` on records assembled by `PolyTimeComputable.append` from the
literal serializations of `clauseLit_poly` codes), combined by `polyTimeComputable_and/or`. -/
theorem polyTimeComputable_memS :
    PolyTimeComputable fun w => [memS (pairSndD w) (pairFstD w).length] := by
  open EncodingMachines in
  have hS := polyTimeComputable_pairSndD
  have hK : PolyTimeComputable fun w => List.replicate (pairSndD w).length true :=
    unaryLength_poly hS
  have hc : PolyTimeComputable fun w => List.replicate (pairFstD w).length true :=
    unaryLength_poly polyTimeComputable_pairFstD
  have hd := fun i => clauseLit_poly hK hc i
  have hl := fun i => polyTimeComputable_serializeLit_litOfCode (hd i)
  have hT := polyTimeComputable_const [true]
  have hF := polyTimeComputable_const [false]
  have hr1 : PolyTimeComputable fun w =>
      clauseRec (candClause (pairSndD w).length (pairFstD w).length 1) :=
    (hT.append ((hl 0).append hF)).congr fun w => by
      rw [candClause_one, clauseRec_eq, Bridge.serializeClause_eq]; simp
  have hr2 : PolyTimeComputable fun w =>
      clauseRec (candClause (pairSndD w).length (pairFstD w).length 2) :=
    (hT.append ((hl 0).append ((hl 1).append hF))).congr fun w => by
      rw [candClause_two, clauseRec_eq, Bridge.serializeClause_eq]; simp
  have hr3 : PolyTimeComputable fun w =>
      clauseRec (candClause (pairSndD w).length (pairFstD w).length 3) :=
    (hT.append ((hl 0).append ((hl 1).append ((hl 2).append hF)))).congr fun w => by
      rw [candClause_three, clauseRec_eq, Bridge.serializeClause_eq]; simp
  have hv1 : PolyTimeComputable fun w => [candValid (pairSndD w).length (pairFstD w).length 1] :=
    polyTimeComputable_and (eqTest_poly (hd 0) (hd 1)) (eqTest_poly (hd 1) (hd 2))
  have hv2 : PolyTimeComputable fun w => [candValid (pairSndD w).length (pairFstD w).length 2] :=
    eqTest_poly (hd 1) (hd 2)
  have hv3 : PolyTimeComputable fun w => [candValid (pairSndD w).length (pairFstD w).length 3] :=
    polyTimeComputable_const [true]
  refine (polyTimeComputable_and (polyTimeComputable_syntaxOK.comp' hS)
    (polyTimeComputable_or (polyTimeComputable_or
      (polyTimeComputable_and hv1 (polyTimeComputable_hasRec hS hr1))
      (polyTimeComputable_and hv2 (polyTimeComputable_hasRec hS hr2)))
      (polyTimeComputable_and hv3 (polyTimeComputable_hasRec hS hr3)))).congr fun w => ?_
  rw [memS_eq, memAlg_eq]

/-! ### The width automaton and `goodS` -/

/-- **The width automaton**: on the state `(q, n, bad)` it runs the grammar automaton `q`,
counts the literals `n` of the current clause up to `4` (reset at formula level, incremented
when a literal starts at clause level), and raises `bad` when a clause ends with `0` or `4`
counted literals. -/
def widthStep (st : Fin 6 × Fin 5 × Bool) (b : Bool) : Fin 6 × Fin 5 × Bool :=
  (CNF.syntaxStep st.1 b,
    if st.1 = 0 then 0
    else if st.1 = 1 ∧ b = true then ⟨min (st.2.1.val + 1) 4, by omega⟩ else st.2.1,
    st.2.2 || (decide (st.1 = 1) && !b && decide (st.2.1.val = 0 ∨ st.2.1.val = 4)))

/-- The defining equation of `widthStep`. -/
theorem widthStep_eq (st : Fin 6 × Fin 5 × Bool) (b : Bool) :
    widthStep st b = (CNF.syntaxStep st.1 b,
      if st.1 = 0 then 0
      else if st.1 = 1 ∧ b = true then ⟨min (st.2.1.val + 1) 4, by omega⟩ else st.2.1,
      st.2.2 || (decide (st.1 = 1) && !b && decide (st.2.1.val = 0 ∨ st.2.1.val = 4))) := rfl

/-- Glue: the unary run of a literal stays in the index state. -/
private theorem foldl_widthStep_replicate (n : Fin 5) (β : Bool) (v : ℕ) :
    (List.replicate v true).foldl widthStep (2, n, β) = (2, n, β) := by
  induction v with
  | zero => rfl
  | succ v ih =>
    rw [List.replicate_succ, List.foldl_cons, widthStep_eq, Bridge.syntaxStep_eq]
    simpa using ih

/-- Glue: a literal increments the (capped) literal count at clause level. -/
private theorem foldl_widthStep_lit (n : Fin 5) (β : Bool) (ℓ : Literal ℕ) :
    (CNF.serializeLit ℓ).foldl widthStep (1, n, β) = (1, ⟨min (n.val + 1) 4, by omega⟩, β) := by
  rw [Bridge.serializeLit_eq, List.replicate_succ, List.cons_append, List.foldl_cons,
    List.foldl_append]
  have h1 : widthStep (1, n, β) true = (2, ⟨min (n.val + 1) 4, by omega⟩, β) := by
    rw [widthStep_eq, Bridge.syntaxStep_eq]; simp
  rw [h1, foldl_widthStep_replicate]
  simp [widthStep_eq, Bridge.syntaxStep_eq]

/-- Glue: the literals of a clause add their number to the capped count. -/
private theorem foldl_widthStep_lits (C : CNF.Clause ℕ) (n : Fin 5) (β : Bool) :
    (C.flatMap CNF.serializeLit).foldl widthStep (1, n, β) =
      (1, ⟨min (n.val + C.length) 4, by omega⟩, β) := by
  induction C generalizing n with
  | nil =>
    simp only [List.flatMap_nil, List.foldl_nil, List.length_nil, add_zero, Prod.mk.injEq,
      true_and, and_true]
    rw [Fin.ext_iff]
    show (n : ℕ) = min (n : ℕ) 4
    omega
  | cons ℓ C ih =>
    rw [List.flatMap_cons, List.foldl_append, foldl_widthStep_lit, ih]
    simp only [List.length_cons, Prod.mk.injEq, true_and, and_true]
    ext; simp only; omega

/-- Glue: the capped count `min k 4` flags `k = 0` or `k ≥ 4`. -/
private theorem decide_min_bad (k : ℕ) :
    decide (min k 4 = 0 ∨ min k 4 = 4) = !(decide (1 ≤ k) && decide (k ≤ 3)) := by
  rcases Nat.lt_or_ge k 4 with h | h
  · interval_cases k <;> rfl
  · rw [min_eq_right h]
    have : ¬ k ≤ 3 := by omega
    simp [this]

/-- Glue: a clause record returns to formula level and flags a clause with `0` or `≥ 4`
literals. -/
private theorem foldl_widthStep_rec (C : CNF.Clause ℕ) (n : Fin 5) (β : Bool) :
    ∃ m : Fin 5, (clauseRec C).foldl widthStep (0, n, β) =
      (0, m, β || !(decide (1 ≤ C.length) && decide (C.length ≤ 3))) := by
  rw [clauseRec_eq, Bridge.serializeClause_eq, List.foldl_cons, List.foldl_append]
  have h1 : widthStep (0, n, β) true = (1, 0, β) := by
    rw [widthStep_eq, Bridge.syntaxStep_eq]; simp
  rw [h1, foldl_widthStep_lits, List.foldl_cons, List.foldl_nil]
  refine ⟨⟨min (0 + C.length) 4, by omega⟩, ?_⟩
  rw [widthStep_eq, Bridge.syntaxStep_eq]
  simp only [Prod.mk.injEq]
  refine ⟨by simp, by simp, ?_⟩
  dsimp only
  rw [decide_min_bad (((0 : Fin 5) : ℕ) + C.length)]
  simp

/-- Glue: a list of clause records returns to formula level and flags its bad clauses. -/
private theorem foldl_widthStep_recs (χ : CNF ℕ) (n : Fin 5) (β : Bool) :
    ∃ m : Fin 5, (χ.flatMap clauseRec).foldl widthStep (0, n, β) =
      (0, m, β || χ.any fun C => !(decide (1 ≤ C.length) && decide (C.length ≤ 3))) := by
  induction χ generalizing n β with
  | nil => exact ⟨n, by simp⟩
  | cons C χ ih =>
    obtain ⟨m, hm⟩ := foldl_widthStep_rec C n β
    rw [List.flatMap_cons, List.foldl_append, hm]
    obtain ⟨m', hm'⟩ := ih m (β || !(decide (1 ≤ C.length) && decide (C.length ≤ 3)))
    rw [hm']
    exact ⟨m', by simp [Bool.or_assoc]⟩

/-- **`goodS` is its string test**: `goodS s = (!syntaxOK s || !(s.foldl widthStep (0, 0,
false)).2.2)`.

**Proof sketch.** Ill-formed strings decode to `[]`, where `goodS` holds. A well-formed `s` is
`serialize φ` (`eq_serialize_decode`), the records of `φ` followed by `0`, and the width
automaton flags exactly the clauses with `0` or `≥ 4` literals (`foldl_widthStep_recs`). -/
theorem goodS_eq (s : List Bool) :
    goodS s = (!CNF.syntaxOK s || !(s.foldl widthStep (0, 0, false)).2.2) := by
  cases hok : CNF.syntaxOK s with
  | false =>
    simp only [Bool.not_false, Bool.true_or]
    rw [goodS_iff, decode_eq_nil_of_syntaxOK hok]
    simp
  | true =>
    simp only [Bool.not_true, Bool.false_or]
    have hs := eq_serialize_decode hok
    obtain ⟨m, hm⟩ := foldl_widthStep_recs (CNF.decode s) 0 false
    have hrun : (s.foldl widthStep (0, 0, false)).2.2 =
        (CNF.decode s).any fun C => !(decide (1 ≤ C.length) && decide (C.length ≤ 3)) := by
      conv_lhs => rw [hs, serialize_eq_recs, List.foldl_append, hm]
      rw [List.foldl_cons, List.foldl_nil, widthStep_eq]
      simp
    rw [hrun]
    apply Bool.eq_iff_iff.mpr
    rw [goodS_iff]
    simp [Nat.one_le_iff_ne_zero]

/-- **`goodS` is polynomial-time**: `s ↦ [goodS s]` (`goodS_eq`, `polyTimeComputable_syntaxOK`,
`polyTimeComputable_foldl_accept` on `widthStep`). -/
theorem polyTimeComputable_goodS : PolyTimeComputable fun s => [goodS s] :=
  (polyTimeComputable_or (polyTimeComputable_not polyTimeComputable_syntaxOK)
    (polyTimeComputable_not (polyTimeComputable_foldl_accept widthStep (0, 0, false)
      fun st => st.2.2))).congr fun s => by rw [goodS_eq]

/-! ### The instance map -/

/-- **The 3SAT → 3COL instance map is polynomial-time computable**:
`PolyTimeComputable colorInst` (`polyTimeComputable_colorInst_of` with
`polyTimeComputable_memS` and `polyTimeComputable_goodS`). -/
theorem polyTimeComputable_colorInst : PolyTimeComputable colorInst :=
  polyTimeComputable_colorInst_of polyTimeComputable_memS polyTimeComputable_goodS

end TCSlib.Cryptography.LevinHardness
