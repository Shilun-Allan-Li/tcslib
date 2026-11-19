/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.ZeroKnowledge.LevinHardness.Gadget
import TCSlib.Cryptography.ZeroKnowledge.LevinHardness.Relations
import TCSlib.Cryptography.SecureComputation.ComposeSecurity.Machines
import TCSlib.Cryptography.ZeroKnowledge.LevinHardness.UnaryArith
import TCSlib.Complexity.NPReductions.ThreeSATToColoring

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The string-level 3SAT → 3COL instance map

The instance map of the Levin reduction `(3SAT, R_3SAT) → (3COL, R_3COL)` ([AB09, §2.3]; the
gadget of the course reduction `Complexity/NPReductions/ThreeSATToColoring.lean`, course material
of CS 294-268, UC Berkeley, Spring 2026), as an explicit map on binary strings.

A string `s` is read as the formula `CNF.decode s`, whose variables are bounded by `K = |s|`. A
literal `(v, b)` has code `litCode (v, b) = 2v + (if b then 0 else 1)`; a clause of one, two or
three literals is widened to three literals by repeating its last one (`wideLit`), and has clause
code `ℓ₁ + 2K ℓ₂ + (2K)² ℓ₃` (`clauseCode`). When every clause of `CNF.decode s` has one to three
literals (`goodS`), the instance is the adjacency matrix of the gadget graph
`gadgetGraph |s| (memS s)` whose clause gadgets are switched on by the clause codes of the formula
(`memS`); otherwise it is the adjacency matrix of the complete graph `k4` on four vertices, which
is not 3-colourable.

## Main definitions

* `litCode`, `wideLit`, `clauseCode` — the codes of literals and widened clauses.
* `memS`, `goodS` — the clause-code membership test and the width test of a string.
* `k4` — the complete loopless graph on four vertices.
* `colorInst` — the instance map.
* `gadgetSimpleGraph` — the gadget graph as a Mathlib simple graph.
* `litEquiv`, `clauseEquiv`, `vertexEquiv` — the explicit identification of the codes and of the
  vertices `Fin (gadgetN K)` with the literals, clauses and vertices of the course reduction over
  `Fin K`.

## Main results

* `memS_iff`, `goodS_iff` — the specifications of the two tests.
* `clauseLit_code`, `clauseLit_clauseCode`, `clauseSat_clauseCode` — clause codes decode to the
  widened clause, and a code is satisfied iff the clause is.
* `clauseSat_of_memS_of_lt` — a satisfying assignment of `CNF.decode s` satisfies every member code.
* `not_threeColorable_k4` — `k4` is not 3-colourable.
* `encGraph_gadgetGraph` — the gadget adjacency matrix as a tabulation over `i < N²`.
* `polyTimeComputable_gadgetAdj`, `polyTimeComputable_colorInst_of` — the instance map is
  polynomial-time computable once the two tests `memS`, `goodS` are.

## References

* CS 294-268 course material (UC Berkeley, Spring 2026, V. Guruswami), the 3SAT → 3-colouring
  reduction as formalized in `Complexity/NPReductions/ThreeSATToColoring.lean`.
* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Cambridge
  University Press, 2009. (§2.3.)
-/

namespace TCSlib.Cryptography.LevinHardness

open Std.Sat Complexity

/-! ### Literal and clause codes -/

/-- **The code of a literal** `(v, b)`: `litCode (v, b) = 2v + (if b then 0 else 1)` (even codes
are the positive literals). -/
def litCode (ℓ : Literal ℕ) : ℕ := 2 * ℓ.1 + if ℓ.2 then 0 else 1

/-- The defining equation of `litCode`. -/
theorem litCode_eq (ℓ : Literal ℕ) : litCode ℓ = 2 * ℓ.1 + if ℓ.2 then 0 else 1 := rfl

/-- A literal on a variable `v < K` has a code `litCode ℓ < 2K`. Glue. -/
theorem litCode_lt {K : ℕ} {ℓ : Literal ℕ} (h : ℓ.1 < K) : litCode ℓ < 2 * K := by
  rw [litCode_eq]
  split <;> omega

/-- The truth value of the code of a literal is the truth value of the literal:
`litVal val (litCode ℓ) = (val ℓ.1 == ℓ.2)`. Glue. -/
theorem litVal_litCode (val : ℕ → Bool) (ℓ : Literal ℕ) :
    litVal val (litCode ℓ) = (val ℓ.1 == ℓ.2) := by
  obtain ⟨v, b⟩ := ℓ
  rw [litVal_eq, litCode_eq]
  cases b
  · have h1 : (2 * v + 1) % 2 = 1 := by omega
    have h2 : (2 * v + 1) / 2 = v := by omega
    simp only [Bool.false_eq_true, ↓reduceIte, h1, h2, one_ne_zero]
    cases val v <;> rfl
  · have h1 : (2 * v + 0) % 2 = 0 := by omega
    have h2 : (2 * v + 0) / 2 = v := by omega
    simp only [↓reduceIte, h1, h2]
    cases val v <;> rfl

/-- **The `j`-th literal of the widening of a clause** to three literals: the clause's literal
number `min j (|C| - 1)` (its last literal repeated), `wideLit C j = C.getD (min j (|C| - 1))
(0, true)`. -/
def wideLit (C : CNF.Clause ℕ) (j : ℕ) : Literal ℕ := C.getD (min j (C.length - 1)) (0, true)

/-- The defining equation of `wideLit`. -/
theorem wideLit_eq (C : CNF.Clause ℕ) (j : ℕ) :
    wideLit C j = C.getD (min j (C.length - 1)) (0, true) := rfl

/-- Every literal of the widening of a nonempty clause is a literal of the clause. Glue. -/
theorem wideLit_mem {C : CNF.Clause ℕ} (hC : 1 ≤ C.length) (j : ℕ) : wideLit C j ∈ C := by
  rw [wideLit_eq, List.getD_eq_getElem _ _ (by omega)]
  exact List.getElem_mem _

/-- Every literal of a clause of at most three literals occurs in its widening:
`ℓ ∈ C → ∃ j < 3, wideLit C j = ℓ`. Glue. -/
theorem exists_wideLit_eq {C : CNF.Clause ℕ} (hC : C.length ≤ 3) {ℓ : Literal ℕ}
    (hℓ : ℓ ∈ C) : ∃ j < 3, wideLit C j = ℓ := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hℓ
  refine ⟨i, by omega, ?_⟩
  rw [wideLit_eq, List.getD_eq_getElem _ _ (by omega)]
  congr 1
  omega

/-- **The code of a clause** for `K` variables: the codes `ℓ₁, ℓ₂, ℓ₃` of its widening, combined
as `clauseCode K C = ℓ₁ + 2K ℓ₂ + (2K)² ℓ₃`. -/
def clauseCode (K : ℕ) (C : CNF.Clause ℕ) : ℕ :=
  litCode (wideLit C 0) + 2 * K * litCode (wideLit C 1) + (2 * K) ^ 2 * litCode (wideLit C 2)

/-- The defining equation of `clauseCode`. -/
theorem clauseCode_eq (K : ℕ) (C : CNF.Clause ℕ) :
    clauseCode K C = litCode (wideLit C 0) + 2 * K * litCode (wideLit C 1) +
      (2 * K) ^ 2 * litCode (wideLit C 2) := rfl

/-- **The literals of a three-digit code** `a + 2K b + (2K)² d` with `a, b, d < 2K` are its
digits: `clauseLit K (a + 2K b + (2K)² d) j = [a, b, d]_j`. Glue.

**Proof sketch.** Write `m = 2K`. The code is `a + m (b + m d)`, so its remainder mod `m` is `a`
and its quotient by `m` is `b + m d`, whose remainder is `b`; its quotient by `m²` is `d` because
`a + m b < m²`. -/
theorem clauseLit_code {K a b d : ℕ} (ha : a < 2 * K) (hb : b < 2 * K) (hd : d < 2 * K)
    (j : Fin 3) :
    clauseLit K (a + 2 * K * b + (2 * K) ^ 2 * d) j = ![a, b, d] j := by
  set m := 2 * K with hm
  have hm0 : 0 < m := by omega
  have hx : a + m * b + m ^ 2 * d = a + m * (b + m * d) := by ring
  have hdiv : (a + m * (b + m * d)) / m = b + m * d := by
    rw [Nat.add_mul_div_left _ _ hm0, Nat.div_eq_of_lt ha, zero_add]
  have hlow : a + m * b < m ^ 2 := by nlinarith
  rw [clauseLit_eq, ← hm, hx]
  fin_cases j
  · simp only [Fin.zero_eta, Fin.isValue, Fin.reduceEq, ↓reduceIte, pow_zero, Nat.div_one,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ha, Matrix.cons_val_zero]
  · simp only [Fin.mk_one, Fin.isValue, Fin.reduceEq, ↓reduceIte, pow_one, hdiv,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hb, Matrix.cons_val_one, Matrix.cons_val_zero]
  · simp only [Fin.reduceFinMk, Fin.isValue, ↓reduceIte, Matrix.cons_val_two,
      Matrix.tail_cons, Matrix.head_cons]
    rw [← hx, show a + m * b + m ^ 2 * d = (a + m * b) + m ^ 2 * d by ring,
      Nat.add_mul_div_left _ _ (by positivity), Nat.div_eq_of_lt hlow, zero_add]

/-- **A clause code decodes to the widened clause**: if every variable of the nonempty clause `C`
is `< K`, then `clauseLit K (clauseCode K C) j = litCode (wideLit C j)`. Glue. -/
theorem clauseLit_clauseCode {K : ℕ} {C : CNF.Clause ℕ} (hK : ∀ ℓ ∈ C, ℓ.1 < K)
    (hC : 1 ≤ C.length) (j : Fin 3) :
    clauseLit K (clauseCode K C) j = litCode (wideLit C j) := by
  have h : ∀ i, litCode (wideLit C i) < 2 * K := fun i => litCode_lt (hK _ (wideLit_mem hC i))
  rw [clauseCode_eq, clauseLit_code (h 0) (h 1) (h 2)]
  fin_cases j <;> rfl

/-- **A clause is true iff one of its literals is**: a clause evaluates to `true` under `val`
iff one of its literals `(v, b)` has `val v = b`,
`C.eval val = true ↔ ∃ ℓ ∈ C, (val ℓ.1 == ℓ.2) = true` (Std `CNF.Clause.eval_cons`). Glue. -/
theorem clause_eval_eq_true_iff (val : ℕ → Bool) (C : CNF.Clause ℕ) :
    C.eval val = true ↔ ∃ ℓ ∈ C, (val ℓ.1 == ℓ.2) = true := by
  induction C with
  | nil => simp [CNF.Clause.eval_nil]
  | cons ℓ C ih => simp [CNF.Clause.eval_cons, ih]

/-- **A formula is true iff all its clauses are**: a CNF evaluates to `true` under `val` iff
every clause does, `φ.eval val = true ↔ ∀ C ∈ φ, C.eval val = true` (Std `CNF.eval_cons`).
Glue. -/
theorem cnf_eval_eq_true_iff (val : ℕ → Bool) (φ : CNF ℕ) :
    φ.eval val = true ↔ ∀ C ∈ φ, C.eval val = true := by
  induction φ with
  | nil => simp [CNF.eval_nil]
  | cons C φ ih => simp [CNF.eval_cons, ih]

/-- **A clause code is satisfied iff its clause is**: for a clause `C` of one to three literals
on variables `< K`, `clauseSat K val (clauseCode K C) = C.eval val`. Glue.

**Proof sketch.** The three literal codes of `clauseCode K C` are the codes of the widened
literals (`clauseLit_clauseCode`), whose truth values are those of the literals
(`litVal_litCode`); the widened literals are literals of `C` (`wideLit_mem`) and every literal of
`C` is one of them (`exists_wideLit_eq`). -/
theorem clauseSat_clauseCode {K : ℕ} (val : ℕ → Bool) {C : CNF.Clause ℕ}
    (hK : ∀ ℓ ∈ C, ℓ.1 < K) (h1 : 1 ≤ C.length) (h3 : C.length ≤ 3) :
    clauseSat K val (clauseCode K C) = C.eval val := by
  apply Bool.eq_iff_iff.mpr
  rw [clause_eval_eq_true_iff, clauseSat_eq]
  simp only [clauseLit_clauseCode hK h1, litVal_litCode, Bool.or_eq_true]
  constructor
  · rintro ((h | h) | h)
    · exact ⟨_, wideLit_mem h1 0, h⟩
    · exact ⟨_, wideLit_mem h1 1, h⟩
    · exact ⟨_, wideLit_mem h1 2, h⟩
  · rintro ⟨ℓ, hℓ, h⟩
    obtain ⟨j, hj, rfl⟩ := exists_wideLit_eq h3 hℓ
    interval_cases j
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr h)
    · exact Or.inr h

/-! ### The two tests of a string -/

/-- **The clause-membership test of a string**: `memS s c` holds when `c` is the code
`clauseCode |s| C` of a clause `C` of `CNF.decode s` with `1 ≤ |C| ≤ 3`. -/
def memS (s : List Bool) (c : ℕ) : Bool :=
  (CNF.decode s).any fun C =>
    decide (1 ≤ C.length) && decide (C.length ≤ 3) && decide (clauseCode s.length C = c)

/-- **Specification of `memS`**: `memS s c = true ↔ ∃ C ∈ CNF.decode s, 1 ≤ C.length ∧
C.length ≤ 3 ∧ clauseCode s.length C = c`. -/
theorem memS_iff (s : List Bool) (c : ℕ) :
    memS s c = true ↔ ∃ C ∈ CNF.decode s, 1 ≤ C.length ∧ C.length ≤ 3 ∧
      clauseCode s.length C = c := by
  simp [memS, and_assoc]

/-- **The width test of a string**: `goodS s` holds when every clause of `CNF.decode s` has one
to three literals. -/
def goodS (s : List Bool) : Bool :=
  (CNF.decode s).all fun C => decide (1 ≤ C.length) && decide (C.length ≤ 3)

/-- **Specification of `goodS`**: `goodS s = true ↔ ∀ C ∈ CNF.decode s, 1 ≤ C.length ∧
C.length ≤ 3`. -/
theorem goodS_iff (s : List Bool) :
    goodS s = true ↔ ∀ C ∈ CNF.decode s, 1 ≤ C.length ∧ C.length ≤ 3 := by
  simp [goodS]

/-- **A satisfying assignment satisfies every member code**: if every variable of
`CNF.decode s` is `< |s|` and `(CNF.decode s).eval val = true`, then `memS s c = true` implies
`clauseSat |s| val c = true` (the bridge from 3SAT witnesses to the gadget colouring). Glue. -/
theorem clauseSat_of_memS_of_lt {s : List Bool} {val : ℕ → Bool} {c : ℕ}
    (hK : ∀ C ∈ CNF.decode s, ∀ ℓ ∈ C, ℓ.1 < s.length)
    (heval : (CNF.decode s).eval val = true) (hm : memS s c = true) :
    clauseSat s.length val c = true := by
  obtain ⟨C, hC, h1, h3, rfl⟩ := (memS_iff s c).1 hm
  rw [clauseSat_clauseCode val (hK C hC) h1 h3]
  exact (cnf_eval_eq_true_iff val _).1 heval C hC

/-! ### The complete graph on four vertices -/

/-- **The complete loopless graph on four vertices**: `k4 u v = decide (u ≠ v)`. -/
def k4 : Graph 4 := fun u v => decide (u ≠ v)

/-- The entries of `k4`: `k4 u v = decide (u ≠ v)`. -/
theorem k4_apply (u v : Fin 4) : k4 u v = decide (u ≠ v) := rfl

/-- **`k4` is not 3-colourable**: a proper colouring `Fin 4 → Fin 3` of the complete graph would
be injective (pigeonhole, `Fintype.card_le_of_injective`). -/
theorem not_threeColorable_k4 : ¬ ThreeColorable k4 := by
  rw [threeColorable_iff]
  rintro ⟨c, hc⟩
  have hinj : Function.Injective c := by
    intro u v huv
    by_contra hne
    exact (hc.ne (by rw [k4_apply]; exact decide_eq_true hne)) huv
  have := Fintype.card_le_of_injective c hinj
  simp at this

/-! ### The instance map -/

/-- **The 3SAT → 3COL instance map** on strings: the adjacency matrix of the gadget graph
`gadgetGraph |s| (memS s)` when every clause of `CNF.decode s` has one to three literals
(`goodS s`), and of `k4` otherwise:
`colorInst s = if goodS s then encGraph (gadgetGraph |s| (memS s)) else encGraph k4`. -/
def colorInst (s : List Bool) : List Bool :=
  if goodS s then encGraph (gadgetGraph s.length (memS s)) else encGraph k4

/-- The defining equation of `colorInst`. -/
theorem colorInst_eq (s : List Bool) :
    colorInst s = if goodS s then encGraph (gadgetGraph s.length (memS s)) else encGraph k4 :=
  rfl

/-! ### The adjacency matrix as a tabulation -/

/-- **The gadget adjacency matrix is a tabulation over `i < N²`**: with `N = gadgetN K`,
`encGraph (gadgetGraph K mem) = (List.range (N * N)).flatMap fun i =>
[gadgetAdj K mem (i / N) (i % N)]` (row-major order, `encGraph_getD_nat`). Glue. -/
theorem encGraph_gadgetGraph (K : ℕ) (mem : ℕ → Bool) :
    encGraph (gadgetGraph K mem) = (List.range (gadgetN K * gadgetN K)).flatMap fun i =>
      [gadgetAdj K mem (i / gadgetN K) (i % gadgetN K)] := by
  set N := gadgetN K with hN
  have hN0 : 0 < N := by rw [hN, gadgetN_eq]; omega
  have hmap : ((List.range (N * N)).flatMap fun i => [gadgetAdj K mem (i / N) (i % N)]) =
      (List.range (N * N)).map fun i => gadgetAdj K mem (i / N) (i % N) :=
    List.map_eq_flatMap.symm
  rw [hmap]
  apply List.ext_getElem (by rw [length_encGraph, List.length_map, List.length_range])
  intro i h1 h2
  have hi : i < N * N := by rwa [length_encGraph] at h1
  have hu : i / N < N := (Nat.div_lt_iff_lt_mul hN0).2 hi
  have hv : i % N < N := Nat.mod_lt _ hN0
  have hget := encGraph_getD_nat (gadgetGraph K mem) ⟨i / N, hu⟩ ⟨i % N, hv⟩
  rw [gadgetGraph_apply] at hget
  rw [show i % N + gadgetN K * (i / N) = i from Nat.mod_add_div i N] at hget
  rw [List.getElem_map, List.getElem_range, ← hget, List.getD_eq_getElem _ _ h1]

/-! ### Polynomial time -/

/-- Glue: the in-gadget index-pair test of `gadgetEdge` as a Boolean combination of equalities. -/
private theorem decide_mem_gadgetPairs (a b : ℕ) :
    decide ((a, b) ∈ [(0, 1), (0, 2), (1, 2), (2, 3), (3, 4), (3, 5), (4, 5)]) =
      (decide (a = 0) && decide (b = 1) || decide (a = 0) && decide (b = 2) ||
        decide (a = 1) && decide (b = 2) || decide (a = 2) && decide (b = 3) ||
        decide (a = 3) && decide (b = 4) || decide (a = 3) && decide (b = 5) ||
        decide (a = 4) && decide (b = 5)) := by
  simp only [List.mem_cons, Prod.mk.injEq, List.mem_nil_iff, or_false]
  simp only [Bool.decide_or, Bool.decide_and]
  simp only [Bool.or_assoc]

/-- **The gadget adjacency is a polynomial-time test** of unary data: if `K`, `t`, `t'` are unary
functions and the membership test `mem x (c x)` is polynomial-time for every unary `c`, then
`x ↦ [gadgetAdj (K x) (mem x) (t x) (t' x)]` is polynomial-time computable.

**Proof sketch.** Expand `gadgetAdj_eq` and `gadgetEdge_eq` into `&&`/`||` combinations
(`polyTimeComputable_and`, `polyTimeComputable_or`, `polyTimeComputable_not`) of comparisons of
unary quantities (`EncodingMachines.ltTest_poly`, `leTest_poly`, `eqTest_poly`), built from `K`,
`t`, `t'` and constants by the unary rows (`unaryAdd_poly`, `unarySub_poly`, `unaryMul_poly`,
`divNum_poly`, `modNum_poly`), the literal codes `clauseLit` and the membership test. -/
theorem polyTimeComputable_gadgetAdj {K t t' : List Bool → ℕ} {mem : List Bool → ℕ → Bool}
    (hK : PolyTimeComputable fun x => List.replicate (K x) true)
    (ht : PolyTimeComputable fun x => List.replicate (t x) true)
    (ht' : PolyTimeComputable fun x => List.replicate (t' x) true)
    (hmem : ∀ c : List Bool → ℕ, (PolyTimeComputable fun x => List.replicate (c x) true) →
      PolyTimeComputable fun x => [mem x (c x)]) :
    PolyTimeComputable fun x => [gadgetAdj (K x) (mem x) (t x) (t' x)] := by
  open EncodingMachines in
  have hN : PolyTimeComputable fun x => List.replicate (gadgetN (K x)) true := by
    have hcube : PolyTimeComputable fun x => List.replicate ((2 * K x) ^ 3) true := by
      simpa only [PolyExpr.eval_pow, PolyExpr.eval_var] using
        unaryPolyOf_poly (.pow .var 3) (unaryMul_poly (unaryConst_poly 2) hK)
    simp only [gadgetN_eq]
    exact unaryAdd_poly (unaryAdd_poly (unaryConst_poly 3) (unaryMul_poly (unaryConst_poly 2) hK))
      (unaryMul_poly (unaryConst_poly 6) hcube)
  have hpairs : ∀ a b : List Bool → ℕ, (PolyTimeComputable fun x => List.replicate (a x) true) →
      (PolyTimeComputable fun x => List.replicate (b x) true) →
      PolyTimeComputable fun x =>
        [decide ((a x, b x) ∈ [(0, 1), (0, 2), (1, 2), (2, 3), (3, 4), (3, 5), (4, 5)])] := by
    intro a b ha hb
    simp only [decide_mem_gadgetPairs]
    repeat' first
      | apply polyTimeComputable_or | apply polyTimeComputable_and
      | exact EncodingMachines.eqTest_poly ha (EncodingMachines.unaryConst_poly _)
      | exact EncodingMachines.eqTest_poly hb (EncodingMachines.unaryConst_poly _)
  have h02 : ∀ a : List Bool → ℕ, (PolyTimeComputable fun x => List.replicate (a x) true) →
      PolyTimeComputable fun x => [decide (a x = 0 ∨ a x = 2)] := by
    intro a ha
    simp only [Bool.decide_or]
    exact polyTimeComputable_or (EncodingMachines.eqTest_poly ha (unaryConst_poly 0))
      (EncodingMachines.eqTest_poly ha (unaryConst_poly 2))
  have hE : ∀ u u' : List Bool → ℕ, (PolyTimeComputable fun x => List.replicate (u x) true) →
      (PolyTimeComputable fun x => List.replicate (u' x) true) →
      PolyTimeComputable fun x => [gadgetEdge (K x) (mem x) (u x) (u' x)] := by
    intro u u' hu hu'
    simp only [gadgetEdge_eq, ← divNum_eq, ← modNum_eq]
    repeat' first
      | exact hN | exact hK | exact hu | exact hu'
      | apply divNum_poly | apply modNum_poly
      | apply unaryConst_poly
      | apply polyTimeComputable_or | apply polyTimeComputable_and
      | apply hpairs | apply h02 | apply hmem
      | apply clauseLit_poly
      | apply ltTest_poly | apply leTest_poly | apply eqTest_poly
      | apply unaryAdd_poly | apply unarySub_poly | apply unaryMul_poly
  simp only [gadgetAdj_eq, decide_not]
  exact polyTimeComputable_and (polyTimeComputable_not (eqTest_poly ht ht'))
    (polyTimeComputable_or (hE t t' ht ht') (hE t' t ht' ht))

/-- **The instance map is polynomial-time computable once its two tests are**: if
`⟨1^c, s⟩ ↦ [memS s c]` and `s ↦ [goodS s]` are polynomial-time, then so is `colorInst`.

**Proof sketch.** `colorInst` is `polyTimeComputable_ite` on `goodS` between the constant
`encGraph k4` and the tabulation `encGraph_gadgetGraph`, which is
`ComposeMachines.polyTimeComputable_flatMap_range` over `i < N²` (`N = gadgetN |s|` unary) of the
one-bit chunk `polyTimeComputable_gadgetAdj` at `K = |s|`, `t = i / N`, `t' = i % N`; the
membership test at a unary code `c` is the hypothesis composed with `⟨1^{c}, s⟩`. -/
theorem polyTimeComputable_colorInst_of
    (hmem : PolyTimeComputable fun w => [memS (pairSndD w) (pairFstD w).length])
    (hgood : PolyTimeComputable fun s => [goodS s]) :
    PolyTimeComputable colorInst := by
  open EncodingMachines in
  have hs : PolyTimeComputable fun w : List Bool => List.replicate (pairSndD w).length true :=
    unaryLength_poly polyTimeComputable_pairSndD
  have hi : PolyTimeComputable fun w : List Bool => List.replicate (pairFstD w).length true :=
    unaryLength_poly polyTimeComputable_pairFstD
  have hNu : ∀ {K : List Bool → ℕ}, (PolyTimeComputable fun x => List.replicate (K x) true) →
      PolyTimeComputable fun x => List.replicate (gadgetN (K x)) true := by
    intro K hK
    have hcube : PolyTimeComputable fun x => List.replicate ((2 * K x) ^ 3) true := by
      simpa only [PolyExpr.eval_pow, PolyExpr.eval_var] using
        unaryPolyOf_poly (.pow .var 3) (unaryMul_poly (unaryConst_poly 2) hK)
    simp only [gadgetN_eq]
    exact unaryAdd_poly (unaryAdd_poly (unaryConst_poly 3) (unaryMul_poly (unaryConst_poly 2) hK))
      (unaryMul_poly (unaryConst_poly 6) hcube)
  have hchunk : PolyTimeComputable fun w =>
      [gadgetAdj (pairSndD w).length (memS (pairSndD w))
        ((pairFstD w).length / gadgetN (pairSndD w).length)
        ((pairFstD w).length % gadgetN (pairSndD w).length)] := by
    refine polyTimeComputable_gadgetAdj hs
      ((divNum_poly hi (hNu hs)).congr fun w => by rw [divNum_eq])
      ((modNum_poly hi (hNu hs)).congr fun w => by rw [modNum_eq]) ?_
    intro c hc
    refine (hmem.comp' (hc.pairEncode polyTimeComputable_pairSndD)).congr fun w => ?_
    simp only [pairFstD_pairEncode, pairSndD_pairEncode, List.length_replicate]
  have hG : PolyTimeComputable fun s : List Bool =>
      (List.range (gadgetN s.length * gadgetN s.length)).flatMap fun i =>
        [gadgetAdj s.length (memS s) (i / gadgetN s.length) (i % gadgetN s.length)] :=
    SecureComputation.ComposeMachines.polyTimeComputable_flatMap_range hchunk
      (unaryMul_poly (hNu polyTimeComputable_unary) (hNu polyTimeComputable_unary))
  refine (polyTimeComputable_ite hgood hG (polyTimeComputable_const (encGraph k4))).congr
    fun s => ?_
  rw [colorInst_eq, encGraph_gadgetGraph]

/-! ### The gadget graph as a simple graph -/

/-- **The gadget graph as a Mathlib simple graph** on `Fin (gadgetN K)`: `u ~ v` iff
`gadgetAdj K mem u v = true` (symmetric by `gadgetAdj_comm`, loopless by `gadgetAdj_self`). -/
def gadgetSimpleGraph (K : ℕ) (mem : ℕ → Bool) : SimpleGraph (Fin (gadgetN K)) where
  Adj u v := gadgetAdj K mem u v = true
  symm u v h := by
    change gadgetAdj K mem v u = true
    rw [gadgetAdj_comm]
    exact h
  loopless u h := by
    have h' : gadgetAdj K mem u u = true := h
    rw [gadgetAdj_self] at h'
    exact Bool.false_ne_true h'

/-- The adjacency of `gadgetSimpleGraph`: `u ~ v ↔ gadgetAdj K mem u v = true`. -/
theorem gadgetSimpleGraph_adj (K : ℕ) (mem : ℕ → Bool) (u v : Fin (gadgetN K)) :
    (gadgetSimpleGraph K mem).Adj u v ↔ gadgetAdj K mem u v = true := Iff.rfl

/-- **The gadget graph is 3-colourable iff its simple graph is**:
`ThreeColorable (gadgetGraph K mem) ↔ (gadgetSimpleGraph K mem).Colorable 3` (a Mathlib
`Coloring` into `Fin 3` is a proper 3-colouring). Glue. -/
theorem threeColorable_gadgetGraph_iff (K : ℕ) (mem : ℕ → Bool) :
    ThreeColorable (gadgetGraph K mem) ↔ (gadgetSimpleGraph K mem).Colorable 3 := by
  rw [threeColorable_iff]
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨SimpleGraph.Coloring.mk c fun {u v} h =>
      hc.ne (by rw [gadgetGraph_apply]; exact (gadgetSimpleGraph_adj K mem u v).1 h)⟩
  · rintro ⟨C⟩
    refine ⟨C, (ProperColoring_iff _ _).2 fun u v h => C.valid ?_⟩
    rw [gadgetSimpleGraph_adj, ← gadgetGraph_apply]
    exact h

/-! ### The vertices of the course reduction -/

/-- **Literal codes are the literals of the course reduction** over `Fin K`: the code `ℓ < 2K`
is `pos (ℓ / 2)` for even `ℓ` and `neg (ℓ / 2)` for odd `ℓ`; inversely `pos v ↦ 2v`,
`neg v ↦ 2v + 1`. -/
def litEquiv (K : ℕ) : Fin (2 * K) ≃ SATtoColor.Literal (Fin K) where
  toFun ℓ := if ℓ.val % 2 = 0 then .pos ⟨ℓ.val / 2, by omega⟩ else .neg ⟨ℓ.val / 2, by omega⟩
  invFun
    | .pos v => ⟨2 * v.val, by omega⟩
    | .neg v => ⟨2 * v.val + 1, by omega⟩
  left_inv ℓ := by
    by_cases h : ℓ.val % 2 = 0
    · simp only [h, ↓reduceIte]; ext; simp only; omega
    · simp only [h, ↓reduceIte]; ext; simp only; omega
  right_inv
    | .pos v => by
        simp only [Nat.mul_mod_right, ↓reduceIte, SATtoColor.Literal.pos.injEq]; ext; simp
    | .neg v => by
        have h : (2 * v.val + 1) % 2 ≠ 0 := by omega
        simp only [h, ↓reduceIte, SATtoColor.Literal.neg.injEq]; ext; simp only; omega

/-- The defining equation of `litEquiv`. -/
theorem litEquiv_apply (K : ℕ) (ℓ : Fin (2 * K)) :
    litEquiv K ℓ = if ℓ.val % 2 = 0 then .pos ⟨ℓ.val / 2, by omega⟩
      else .neg ⟨ℓ.val / 2, by omega⟩ := rfl

/-- The code of a positive literal: `(litEquiv K).symm (pos v) = 2v`. -/
theorem litEquiv_symm_pos (K : ℕ) (v : Fin K) :
    (((litEquiv K).symm (.pos v) : Fin (2 * K)) : ℕ) = 2 * v.val := rfl

/-- The code of a negative literal: `(litEquiv K).symm (neg v) = 2v + 1`. -/
theorem litEquiv_symm_neg (K : ℕ) (v : Fin K) :
    (((litEquiv K).symm (.neg v) : Fin (2 * K)) : ℕ) = 2 * v.val + 1 := rfl

/-- Glue: the three literal codes of `c` are `c % 2K`, `c / 2K % 2K` and `c / (2K)²`
(`clauseLit_eq`). -/
private theorem clauseLit_vals (K c : ℕ) :
    clauseLit K c 0 = c % (2 * K) ∧ clauseLit K c 1 = c / (2 * K) % (2 * K) ∧
      clauseLit K c 2 = c / (2 * K) ^ 2 := by
  refine ⟨?_, ?_, ?_⟩ <;> rw [clauseLit_eq] <;> simp

/-- **Every natural number is the three-digit code of its `clauseLit` digits**:
`clauseLit K c 0 + 2K clauseLit K c 1 + (2K)² clauseLit K c 2 = c`. Glue. -/
theorem clauseLit_decomp (K c : ℕ) :
    clauseLit K c 0 + 2 * K * clauseLit K c 1 + (2 * K) ^ 2 * clauseLit K c 2 = c := by
  obtain ⟨e0, e1, e2⟩ := clauseLit_vals K c
  rw [e0, e1, e2]
  set m := 2 * K
  have h1 := Nat.mod_add_div c m
  have h2 := Nat.mod_add_div (c / m) m
  have h3 : c / m ^ 2 = c / m / m := by rw [pow_two, Nat.div_div_eq_div_mul]
  rw [h3]
  calc c % m + m * (c / m % m) + m ^ 2 * (c / m / m)
      = c % m + m * (c / m % m + m * (c / m / m)) := by ring
    _ = c := by rw [h2, h1]

/-- The literal codes of a clause code `c < (2K)³` are literal codes: `clauseLit K c j < 2K`.
Glue. -/
theorem clauseLit_lt {K c : ℕ} (hc : c < (2 * K) ^ 3) (j : Fin 3) : clauseLit K c j < 2 * K := by
  have hm : 0 < 2 * K := by
    rcases Nat.eq_zero_or_pos (2 * K) with h | h
    · rw [h] at hc; simp at hc
    · exact h
  obtain ⟨e0, e1, e2⟩ := clauseLit_vals K c
  fin_cases j
  · exact e0 ▸ Nat.mod_lt _ hm
  · exact e1 ▸ Nat.mod_lt _ hm
  · rw [show ((⟨2, by omega⟩ : Fin 3)) = 2 from rfl, e2, Nat.div_lt_iff_lt_mul (by positivity)]
    calc c < (2 * K) ^ 3 := hc
      _ = 2 * K * (2 * K) ^ 2 := by ring

/-- **A three-digit code with digits `< m` is `< m³`**: `a + m b + m² d < m³`. Glue. -/
theorem code_lt {m a b d : ℕ} (ha : a < m) (hb : b < m) (hd : d < m) :
    a + m * b + m ^ 2 * d < m ^ 3 := by
  have h1 : a + m * b < m ^ 2 := by nlinarith
  have h2 : m ^ 2 * d + m ^ 2 ≤ m ^ 3 := by
    calc m ^ 2 * d + m ^ 2 = m ^ 2 * (d + 1) := by ring
      _ ≤ m ^ 2 * m := Nat.mul_le_mul_left _ hd
      _ = m ^ 3 := by ring
  omega

/-- **Clause codes are below `(2K)³`**: if every variable of the nonempty clause `C` is `< K`,
then `clauseCode K C < (2K)³` (`code_lt` on the three literal codes `< 2K`). Glue. -/
theorem clauseCode_lt {K : ℕ} {C : CNF.Clause ℕ} (hK : ∀ ℓ ∈ C, ℓ.1 < K) (hC : 1 ≤ C.length) :
    clauseCode K C < (2 * K) ^ 3 := by
  have h : ∀ i, litCode (wideLit C i) < 2 * K := fun i => litCode_lt (hK _ (wideLit_mem hC i))
  rw [clauseCode_eq]
  exact code_lt (h 0) (h 1) (h 2)

/-- **Clause codes are the clauses of the course reduction** over `Fin K`: the code
`c < (2K)³` is the clause whose literals are `litEquiv` of `clauseLit K c 0, 1, 2`; inversely
`⟨ℓ₁, ℓ₂, ℓ₃⟩ ↦ ℓ₁ + 2K ℓ₂ + (2K)² ℓ₃` on the literal codes. -/
def clauseEquiv (K : ℕ) : Fin ((2 * K) ^ 3) ≃ SATtoColor.Clause (Fin K) where
  toFun c := ⟨litEquiv K ⟨clauseLit K c 0, clauseLit_lt c.isLt 0⟩,
    litEquiv K ⟨clauseLit K c 1, clauseLit_lt c.isLt 1⟩,
    litEquiv K ⟨clauseLit K c 2, clauseLit_lt c.isLt 2⟩⟩
  invFun C := ⟨((litEquiv K).symm C.l1 : ℕ) + 2 * K * ((litEquiv K).symm C.l2 : ℕ) +
      (2 * K) ^ 2 * ((litEquiv K).symm C.l3 : ℕ),
    code_lt ((litEquiv K).symm C.l1).isLt ((litEquiv K).symm C.l2).isLt
      ((litEquiv K).symm C.l3).isLt⟩
  left_inv c := by
    ext
    simp only [Equiv.symm_apply_apply]
    exact clauseLit_decomp K c
  right_inv C := by
    obtain ⟨l1, l2, l3⟩ := C
    have ha := ((litEquiv K).symm l1).isLt
    have hb := ((litEquiv K).symm l2).isLt
    have hd := ((litEquiv K).symm l3).isLt
    simp only [SATtoColor.Clause.mk.injEq]
    refine ⟨?_, ?_, ?_⟩
    · conv_rhs => rw [← (litEquiv K).apply_symm_apply l1]
      congr 1; ext; simpa using clauseLit_code ha hb hd 0
    · conv_rhs => rw [← (litEquiv K).apply_symm_apply l2]
      congr 1; ext; simpa using clauseLit_code ha hb hd 1
    · conv_rhs => rw [← (litEquiv K).apply_symm_apply l3]
      congr 1; ext; simpa using clauseLit_code ha hb hd 2

/-- The defining equation of `clauseEquiv`: the literals of the clause of code `c` are
`litEquiv K` of `clauseLit K c 0, 1, 2`. -/
theorem clauseEquiv_apply (K : ℕ) (c : Fin ((2 * K) ^ 3)) :
    clauseEquiv K c = ⟨litEquiv K ⟨clauseLit K c 0, clauseLit_lt c.isLt 0⟩,
      litEquiv K ⟨clauseLit K c 1, clauseLit_lt c.isLt 1⟩,
      litEquiv K ⟨clauseLit K c 2, clauseLit_lt c.isLt 2⟩⟩ := rfl

/-- The code of a clause: `(clauseEquiv K).symm C = ℓ₁ + 2K ℓ₂ + (2K)² ℓ₃` for the literal codes
`ℓᵢ = (litEquiv K).symm C.lᵢ`. -/
theorem clauseEquiv_symm_val (K : ℕ) (C : SATtoColor.Clause (Fin K)) :
    (((clauseEquiv K).symm C : Fin ((2 * K) ^ 3)) : ℕ) =
      ((litEquiv K).symm C.l1 : ℕ) + 2 * K * ((litEquiv K).symm C.l2 : ℕ) +
        (2 * K) ^ 2 * ((litEquiv K).symm C.l3 : ℕ) := rfl

/-- **The literal codes of the code of a clause** are the codes of its literals:
`clauseLit K ((clauseEquiv K).symm C) j = (litEquiv K).symm (![C.l1, C.l2, C.l3] j)`. Glue. -/
theorem clauseLit_clauseEquiv_symm (K : ℕ) (C : SATtoColor.Clause (Fin K)) (j : Fin 3) :
    clauseLit K ((clauseEquiv K).symm C) j = ((litEquiv K).symm (![C.l1, C.l2, C.l3] j) : ℕ) := by
  rw [clauseEquiv_symm_val, clauseLit_code ((litEquiv K).symm C.l1).isLt
    ((litEquiv K).symm C.l2).isLt ((litEquiv K).symm C.l3).isLt]
  fin_cases j <;> rfl

/-- Glue: the clause index of a gadget vertex is a clause code. -/
private theorem gadgetIdx_lt {K t : ℕ} (hL : 3 + 2 * K ≤ t) (ht : t < gadgetN K) :
    (t - (3 + 2 * K)) / 6 < (2 * K) ^ 3 := by
  rw [gadgetN_eq] at ht
  generalize (2 * K) ^ 3 = X at ht ⊢
  omega

/-- Glue: the vertex of a gadget node lies below `gadgetN K`. -/
private theorem gadgetVertex_lt {K c i : ℕ} (hc : c < (2 * K) ^ 3) (hi : i < 6) :
    3 + 2 * K + 6 * c + i < gadgetN K := by
  rw [gadgetN_eq]
  generalize (2 * K) ^ 3 = X at hc ⊢
  omega

/-- **The vertices of the gadget graph are the vertices of the course reduction** over `Fin K`:
`t < 3` is the palette vertex `t`; `3 ≤ t < 3 + 2K` is the literal node of code `t - 3`; and
`t = 3 + 2K + 6c + i` (`i < 6`) is gadget node `i` of the clause of code `c`. -/
def vertexEquiv (K : ℕ) : Fin (gadgetN K) ≃ SATtoColor.OutputVertex (Fin K) where
  toFun t :=
    if h : t.val < 3 then .palette ⟨t.val, h⟩
    else if h' : t.val < 3 + 2 * K then .literalNode (litEquiv K ⟨t.val - 3, by omega⟩)
    else .clauseGadget (clauseEquiv K ⟨(t.val - (3 + 2 * K)) / 6, gadgetIdx_lt (by omega) t.isLt⟩)
      ⟨(t.val - (3 + 2 * K)) % 6, by omega⟩
  invFun
    | .palette p => ⟨p.val, by rw [gadgetN_eq]; omega⟩
    | .literalNode l => ⟨3 + ((litEquiv K).symm l).val, by
        have := ((litEquiv K).symm l).isLt
        rw [gadgetN_eq]
        omega⟩
    | .clauseGadget c i => ⟨3 + 2 * K + 6 * ((clauseEquiv K).symm c).val + i.val,
        gadgetVertex_lt ((clauseEquiv K).symm c).isLt i.isLt⟩
  left_inv t := by
    by_cases h1 : t.val < 3
    · simp only [h1, ↓reduceDIte]
    · by_cases h2 : t.val < 3 + 2 * K
      · simp only [h1, h2, ↓reduceDIte, Equiv.symm_apply_apply]
        ext; simp only; omega
      · simp only [h1, h2, ↓reduceDIte, Equiv.symm_apply_apply]
        ext; simp only; omega
  right_inv v := by
    rcases v with p | l | ⟨c, i⟩
    · have h1 : p.val < 3 := p.isLt
      simp only [h1, ↓reduceDIte]
    · have hl := ((litEquiv K).symm l).isLt
      have h1 : ¬ 3 + ((litEquiv K).symm l).val < 3 := by omega
      have h2 : 3 + ((litEquiv K).symm l).val < 3 + 2 * K := by omega
      simp only [h1, h2, ↓reduceDIte, SATtoColor.OutputVertex.literalNode.injEq]
      conv_rhs => rw [← (litEquiv K).apply_symm_apply l]
      congr 1; ext; simp only; omega
    · have hi := i.isLt
      have h1 : ¬ 3 + 2 * K + 6 * ((clauseEquiv K).symm c).val + i.val < 3 := by omega
      have h2 : ¬ 3 + 2 * K + 6 * ((clauseEquiv K).symm c).val + i.val < 3 + 2 * K := by omega
      simp only [h1, h2, ↓reduceDIte, SATtoColor.OutputVertex.clauseGadget.injEq]
      constructor
      · conv_rhs => rw [← (clauseEquiv K).apply_symm_apply c]
        congr 1; ext; simp only; omega
      · ext; simp only; omega

/-- The defining equation of `vertexEquiv` (see its docstring for the three ranges). -/
theorem vertexEquiv_apply (K : ℕ) (t : Fin (gadgetN K)) :
    vertexEquiv K t =
      if h : t.val < 3 then .palette ⟨t.val, h⟩
      else if h' : t.val < 3 + 2 * K then .literalNode (litEquiv K ⟨t.val - 3, by omega⟩)
      else .clauseGadget (clauseEquiv K ⟨(t.val - (3 + 2 * K)) / 6, gadgetIdx_lt (by omega) t.isLt⟩)
        ⟨(t.val - (3 + 2 * K)) % 6, by omega⟩ := rfl

/-- The vertex of a palette node: `(vertexEquiv K).symm (palette p) = p`. -/
theorem vertexEquiv_symm_palette (K : ℕ) (p : Fin 3) :
    (((vertexEquiv K).symm (.palette p) : Fin (gadgetN K)) : ℕ) = p.val := rfl

/-- The vertex of a literal node: `(vertexEquiv K).symm (literalNode l) = 3 + (litEquiv K).symm l`.
-/
theorem vertexEquiv_symm_literalNode (K : ℕ) (l : SATtoColor.Literal (Fin K)) :
    (((vertexEquiv K).symm (.literalNode l) : Fin (gadgetN K)) : ℕ) =
      3 + ((litEquiv K).symm l : ℕ) := rfl

/-- The vertex of a gadget node: `(vertexEquiv K).symm (clauseGadget c i) =
3 + 2K + 6 ((clauseEquiv K).symm c) + i`. -/
theorem vertexEquiv_symm_clauseGadget (K : ℕ) (c : SATtoColor.Clause (Fin K)) (i : Fin 6) :
    (((vertexEquiv K).symm (.clauseGadget c i) : Fin (gadgetN K)) : ℕ) =
      3 + 2 * K + 6 * ((clauseEquiv K).symm c : ℕ) + i.val := rfl

end TCSlib.Cryptography.LevinHardness
