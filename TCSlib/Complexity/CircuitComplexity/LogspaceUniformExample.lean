/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import TCSlib.Complexity.CircuitComplexity.LogspaceUniformAdj
import TCSlib.Complexity.SpaceComplexity.UnaryLogspace

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# A logspace-uniform family, via the adjacency representation

A non-vacuity check for `BoolCircuit.DAGCircuitFamily.isLogspaceUniform_iff` [AB09, p. 112].
The family `BoolCircuit.AdjExample.family`, whose `n`-th circuit is the inputs `0, …, n - 1`
followed by one argument-free `∨` gate (the constant `false`) as output, is canonical. Its
`SIZE`, `TYPE` and `EDGE` languages are all of the form "`i < n` and/or `i = n`", decided by
a one-register abstract machine (`BoolCircuit.AdjExample.leA`) calling the decider of
`Complexity.ltLang` (`i < n`, from `TCSlib.Complexity.SpaceComplexity.UnaryLogspace`).
Hence the family is logspace-uniform.

The gate has fan-in `0`. `BoolCircuit.DAGCircuit` allows this, but it lies outside the
fan-in-two model of [AB09, Def 6.1] (where constants are not gates). A fan-in-two variant such
as `Cₙ = ¬x₀` has the edge `0 → n`, whose `EDGE` language needs a decider on pair inputs
`⟨1ⁿ, ⟨bits i, bits j⟩⟩`. That decider is not built here; the example only shows that the
hypotheses of the equivalence can be met.

## Main definitions

* `BoolCircuit.AdjExample.leLang` — the inputs `⟨1ⁿ, bits i⟩` with `i < n ∧ a` or `i = n ∧ b`.
* `BoolCircuit.AdjExample.family` — the example family.

## Main results

* `BoolCircuit.AdjExample.leLang_mem` — `leLang a b ∈ L`.
* `BoolCircuit.AdjExample.family_isLogspaceUniform` — the family is logspace-uniform.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§6.2.1, p. 112.)
-/

namespace BoolCircuit

namespace AdjExample

open Turing Complexity LogProg

/-- The inputs `⟨1ⁿ, bits i⟩` with `i < n` (if `a`) or `i = n` (if `b`). -/
def leLang (a b : Bool) : Language Bool :=
  {y | ∃ n i, y = pairEncode (List.replicate n true) (Nat.bits i) ∧
    ((i < n ∧ a = true) ∨ (i = n ∧ b = true))}

/-- The labels of the comparison machine. -/
inductive Lb where
  | start | test | cmp | inc | eqc | retA | retB | retF
  deriving DecidableEq, Fintype

/-- **The comparison machine** for `leLang a b`: count `c = 0, 1, …`; while `c < n` (asked
of the `ltLang` decider) answer `a` if `c = i`; at `c = n` answer `b` if `c = i`, and `false`
otherwise. -/
def leA (a b : Bool) : ARM 1 1 Lb
  | .start => .valP 0 .test
  | .test => .call 0 .unaryFst [0] .cmp .eqc
  | .cmp => .jeqIn 0 .retA .inc
  | .inc => .inc 0 .test
  | .eqc => .jeqIn 0 .retB .retF
  | .retA => .ret a
  | .retB => .ret b
  | .retF => .ret false

/-- The oracle: membership in `ltLang`. -/
noncomputable def orc : Fin 1 → List Bool → Bool :=
  fun _ V => MultiTapeTM.indicator (ltLang : Set (List Bool)) V

/-- The oracle on `⟨1ⁿ, bits v⟩` answers `v < n`. -/
lemma orc_eq (n v : ℕ) : orc 0 (pairEncode (List.replicate n true) (Nat.bits v)) =
    decide (v < n) := by
  rw [orc, indicator_eq_decide]
  refine decide_eq_decide.mpr ⟨fun ⟨n', v', h, hv⟩ => ?_, fun h => ⟨n, v, rfl, h⟩⟩
  obtain ⟨rfl, hb⟩ := pairEncode_replicate_inj h
  rw [bits_injective hb]; exact hv

/-- The constant register file `c`. -/
lemma upd_const (c d : ℕ) : Function.update (fun _ : Fin 1 => c) 0 d = fun _ => d := by
  funext r; rw [Subsingleton.elim r 0]; simp

/-- **The loop**: from `test` with counter `c ≤ n`, `c ≤ i`, the machine answers membership
of `⟨1ⁿ, bits i⟩` in `leLang a b`.

**Proof sketch.** Induction on `n - c`. At `c = n` the oracle denies `c < n`, and the machine
answers `b` if `i = n` and `false` otherwise (then `i > n`). At `c < n` it answers `a` if
`c = i` (then `i < n`), and otherwise moves to `c + 1`. -/
lemma loop (a b : Bool) (n i : ℕ) : ∀ d c, c + d = n → c ≤ i →
    AHalt (leA a b) orc (pairEncode (List.replicate n true) (Nat.bits i))
      (fun z => PreS (leA a b) (pairEncode (List.replicate n true) (Nat.bits i)) z ∧
        ∀ r, z.2.1 r ≤ 1 * ((pairEncode (List.replicate n true) (Nat.bits i)).length + 1) ^ 1)
      (some .test, fun _ => c, none)
      (decide ((i < n ∧ a = true) ∨ (i = n ∧ b = true))) := by
  set y := pairEncode (List.replicate n true) (Nat.bits i) with hy
  have hl : n ≤ y.length := by simp [hy, pairEncode_eq_dbl, dbl_replicate]; omega
  have hval : ValidPlain y := ⟨n, _, rfl, canon_bits i⟩
  have hG : ∀ (l : Lb) (c : ℕ), c ≤ n → (PreS (leA a b) y (some l, fun _ => c, none) ∧
      ∀ r, (fun _ : Fin 1 => c) r ≤ 1 * (y.length + 1) ^ 1) := by
    intro l c hc
    refine ⟨?_, fun r => by simp; omega⟩
    cases l <;> simp [PreS, leA, hval]
  have hpw : plainWord y = Nat.bits i := plainWord_pairEncode n _
  have hcall : ∀ c, astep (leA a b) orc y (some .test, fun _ => c, none) =
      (some (if c < n then .cmp else .eqc), fun _ => c, none) := by
    intro c
    rw [hy, Complexity.LogProg.astep_call₁ (leA a b) orc (l := .test) rfl n (Nat.bits i), orc_eq]
    simp
  have hjeq : ∀ (l l₁ l₀ : Lb) c, leA a b l = .jeqIn 0 l₁ l₀ →
      astep (leA a b) orc y (some l, fun _ => c, none) =
        (some (if c = i then l₁ else l₀), fun _ => c, none) := by
    intro l l₁ l₀ c hl
    simp [astep, hl, hpw, bits_injective.eq_iff]
  intro d
  induction d with
  | zero =>
    intro c hc hci
    obtain rfl : c = n := by omega
    refine AHalt.step (hG .test c le_rfl) ?_
    rw [hcall, if_neg (lt_irrefl _)]
    refine AHalt.step (hG .eqc c le_rfl) ?_
    rw [hjeq _ _ _ _ rfl]
    by_cases hi : c = i
    · rw [if_pos hi]
      have e : decide ((i < c ∧ a = true) ∨ (i = c ∧ b = true)) = b := by
        cases b <;> simp <;> omega
      rw [e]; exact AHalt.ret rfl (hG .retB c le_rfl)
    · rw [if_neg hi]
      have e : decide ((i < c ∧ a = true) ∨ (i = c ∧ b = true)) = false := by
        simp; omega
      rw [e]; exact AHalt.ret rfl (hG .retF c le_rfl)
  | succ d ih =>
    intro c hc hci
    refine AHalt.step (hG .test c (by omega)) ?_
    rw [hcall, if_pos (by omega)]
    refine AHalt.step (hG .cmp c (by omega)) ?_
    rw [hjeq _ _ _ _ rfl]
    by_cases hi : c = i
    · rw [if_pos hi]
      have e : decide ((i < n ∧ a = true) ∨ (i = n ∧ b = true)) = a := by
        cases a <;> simp <;> omega
      rw [e]; exact AHalt.ret rfl (hG .retA c (by omega))
    · rw [if_neg hi]
      refine AHalt.step (hG .inc c (by omega)) ?_
      simp only [astep, leA, upd_const]
      exact ih (c + 1) (by omega) (by omega)

/-- **`leLang a b` is in `L`**, decided by the comparison machine with the `ltLang` decider.

**Proof sketch.** `arm_decides_poly` with the single decider `ltLang` (in `L` by
`Complexity.ltLang_mem`). A malformed input is rejected at once (no member is malformed). On
`⟨1ⁿ, bits i⟩` the loop (`loop`) answers membership, the counter staying at most `n ≤ |x|`. -/
theorem leLang_mem (a b : Bool) : leLang a b ∈ LOGSPACE := by
  refine arm_decides_poly (leA a b) .start (fun _ => ltLang) (fun _ => ltLang_mem) 1 1
    fun y => ?_
  by_cases hv : ValidPlain y
  · obtain ⟨n, w, rfl, hw⟩ := hv
    rw [canon_eq_bits w hw]
    set i := bitsVal w
    have hval : ValidPlain (pairEncode (List.replicate n true) (Nat.bits i)) :=
      ⟨n, _, rfl, canon_bits i⟩
    have hans : MultiTapeTM.indicator (leLang a b : Set (List Bool))
        (pairEncode (List.replicate n true) (Nat.bits i)) =
        decide ((i < n ∧ a = true) ∨ (i = n ∧ b = true)) := by
      rw [indicator_eq_decide]
      refine decide_eq_decide.mpr ⟨fun ⟨n', i', h, hp⟩ => ?_, fun h => ⟨n, i, rfl, h⟩⟩
      obtain ⟨rfl, hb⟩ := pairEncode_replicate_inj h
      rw [bits_injective hb]; exact hp
    rw [hans]
    refine AHalt.step ⟨by simp [PreS, leA], fun r => by simp⟩ ?_
    have : astep (leA a b) orc (pairEncode (List.replicate n true) (Nat.bits i))
        (some .start, fun _ => 0, none) = (some .test, fun _ => 0, none) := by
      simp [astep, leA, hval]
    exact this ▸ loop a b n i n 0 (by omega) (Nat.zero_le _)
  · have hn : MultiTapeTM.indicator (leLang a b : Set (List Bool)) y = false := by
      rw [indicator_eq_decide]
      simp only [decide_eq_false_iff_not]
      rintro ⟨n, i, rfl, -⟩
      exact hv ⟨n, _, rfl, canon_bits i⟩
    rw [hn]
    refine ⟨1, by simp [arun, astep, leA, hv], by simp [arun, astep, leA, hv],
      fun t ht => ?_⟩
    obtain rfl : t = 0 := by omega
    exact ⟨by simp [arun, PreS, leA], fun r => by simp [arun]⟩

/-- **The example family**: `Cₙ` has the inputs `0, …, n - 1` and one argument-free `∨`
gate (the constant `false`) at vertex `n`, which is the output. -/
def family : DAGCircuitFamily :=
  ⟨fun n => constCircuit n false⟩

/-- The example family is canonical. -/
lemma family_isCanonical : family.IsCanonical := fun n =>
  ⟨fun g hg => by simp [family, constCircuit] at hg; subst hg; simp,
    by simp [family, constCircuit, DAGCircuit.size]⟩

/-- The example family computes the constant `false`. -/
lemma family_eval (n : ℕ) (x : Fin n → Bool) : (family.circuit n).eval x = false := by
  simp [family]

/-- **The example family is logspace-uniform**, via its adjacency representation
[AB09, p. 112].

**Proof sketch.** Its vertices are `i ≤ n`, its inputs `i < n`, its only gate (an `∨`) is
`i = n`, and it has no edges. So `SIZE`, `TYPE` and `EDGE` are the languages
`leLang a b` for suitable `a, b` (`EDGE` and the other types being empty), all in `L` by
`leLang_mem`. The size is `n + 1`, polynomial. `isLogspaceUniform_iff` concludes. -/
theorem family_isLogspaceUniform : family.IsLogspaceUniform := by
  have hS : family.sizeLang = leLang true true := by
    ext y; simp only [DAGCircuitFamily.sizeLang, leLang, family, constCircuit, DAGCircuit.size]
    simp only [List.length_singleton, and_true]
    constructor
    · rintro ⟨n, i, rfl, h⟩; exact ⟨n, i, rfl, by omega⟩
    · rintro ⟨n, i, rfl, h⟩; exact ⟨n, i, rfl, by omega⟩
  have hT : ∀ t, family.typeLang t =
      leLang (decide (t = none)) (decide (t = some .or)) := by
    intro t; ext y
    simp only [DAGCircuitFamily.typeLang, leLang, family, constCircuit, constGate, DAGCircuit.size,
      DAGCircuit.vtype,
      List.length_singleton, decide_eq_true_eq]
    constructor
    · rintro ⟨n, i, rfl, hi, ht⟩
      refine ⟨n, i, rfl, ?_⟩
      by_cases h : i < n
      · simp only [h, ↓reduceIte] at ht; exact Or.inl ⟨h, ht.symm⟩
      · simp only [h, ↓reduceIte] at ht
        obtain rfl : i = n := by omega
        simp at ht; exact Or.inr ⟨rfl, ht.symm⟩
    · rintro ⟨n, i, rfl, h⟩
      refine ⟨n, i, rfl, ?_⟩
      rcases h with ⟨h, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨by omega, by simp [h]⟩
      · exact ⟨by omega, by simp⟩
  have hE : family.edgeLang = leLang false false := by
    ext y; simp only [DAGCircuitFamily.edgeLang, leLang]
    constructor
    · rintro ⟨n, i, j, rfl, -, g, hg, hi⟩
      have : g.args = [] := by
        simp only [family, constCircuit, constGate] at hg
        rcases List.getElem?_eq_some_iff.mp hg with ⟨hlt, rfl⟩
        simp at hlt; simp [show j - n = 0 by omega]
      simp [this] at hi
    · rintro ⟨n, i, rfl, h⟩; simp at h
  refine (DAGCircuitFamily.isLogspaceUniform_iff family_isCanonical).mpr
    ⟨⟨1, 1, fun n => by simp [family, constCircuit, DAGCircuit.size]⟩, hS ▸ leLang_mem _ _,
      fun t => (hT t) ▸ leLang_mem _ _, hE ▸ leLang_mem _ _⟩

end AdjExample

end BoolCircuit
