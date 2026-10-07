/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hydroxyi
-/
import Mathlib.Tactic.FinCases
import TCSlib.Complexity.SpaceComplexity.Machines.DblLang

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Functions of the unary length computable in logarithmic space

A uniformity function only matters on the inputs `1ⁿ` [AB09, Def 6.14]. For a sequence of
words `g : ℕ → List Bool` (the value on `1ⁿ`) this file defines the bit and length
languages `{⟨1ⁿ, bits i⟩ | g(n)ᵢ = 1}`, `{⟨1ⁿ, bits i⟩ | i < |g(n)|}` and calls `g`
*unary-logspace* when both are in `L`; with a polynomial length bound this makes the
extension of `g` by `[]` off unary inputs implicitly logspace computable [AB09, Def 4.16].
The first example is `g(n) = 1ⁿ`, decided by an abstract register machine that counts
`k = 0, 1, …` and asks the base decider `dblLang` whether `2k = 2n`.

These pieces (`ltLang`, `UnaryLogspace`, `unaryExt`, and the counter-program simulation of
`TCSlib.Complexity.SpaceComplexity.CounterProgSim`) are generic logspace material; their
first client is [AB09, Thm 6.15] (`TCSlib.Complexity.CircuitComplexity.LogspaceTableau`).

## Main definitions

* `Complexity.uBit`, `Complexity.uLen` — the bit and length languages of `g`.
* `Complexity.UnaryLogspace g` — both are in `L`.
* `Complexity.unaryExt g` — `g |x|` on unary `x`, `[]` elsewhere.

## Main results

* `Complexity.UnaryLogspace.implicitlyLogspaceComputable` — with a polynomial length bound,
  `unaryExt g` is implicitly logspace computable.
* `Complexity.unaryLogspace_replicate` — `n ↦ 1ⁿ` is unary-logspace.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009. (§4.1; §4.3, Definition 4.16; §6.2.1, Definition 6.14.)
-/

namespace Complexity

open Turing LogProg

/-! ## Unary index languages -/

/-- The bit language of `g`: `⟨1ⁿ, bits i⟩` with `g(n)ᵢ = 1`. -/
def uBit (g : ℕ → List Bool) : Language Bool :=
  {y | ∃ n i, y = pairEncode (List.replicate n true) (Nat.bits i) ∧ (g n).getD i false = true}

/-- The length language of `g`: `⟨1ⁿ, bits i⟩` with `i < |g(n)|`. -/
def uLen (g : ℕ → List Bool) : Language Bool :=
  {y | ∃ n i, y = pairEncode (List.replicate n true) (Nat.bits i) ∧ i < (g n).length}

/-- `g` is *unary-logspace*: its bit and length languages are in `L`. -/
def UnaryLogspace (g : ℕ → List Bool) : Prop :=
  uBit g ∈ LOGSPACE ∧ uLen g ∈ LOGSPACE

/-- Membership of `⟨1ⁿ, bits i⟩` in a language of the form `{⟨1ⁿ, bits i⟩ | p n i}`. -/
lemma mem_unaryIdx (p : ℕ → ℕ → Prop) (n i : ℕ) :
    pairEncode (List.replicate n true) (Nat.bits i) ∈
        {y : List Bool | ∃ n i, y = pairEncode (List.replicate n true) (Nat.bits i) ∧ p n i} ↔
      p n i := by
  constructor
  · rintro ⟨n', i', h, hp⟩
    obtain ⟨rfl, hb⟩ := pairEncode_replicate_inj h
    rwa [bits_injective hb]
  · exact fun h => ⟨n, i, rfl, h⟩

/-- Membership in the bit language. -/
lemma mem_uBit (g : ℕ → List Bool) (n i : ℕ) :
    pairEncode (List.replicate n true) (Nat.bits i) ∈ uBit g ↔ (g n).getD i false = true :=
  mem_unaryIdx (fun n i => (g n).getD i false = true) n i

/-- Membership in the length language. -/
lemma mem_uLen (g : ℕ → List Bool) (n i : ℕ) :
    pairEncode (List.replicate n true) (Nat.bits i) ∈ uLen g ↔ i < (g n).length :=
  mem_unaryIdx (fun n i => i < (g n).length) n i

/-- Members of a unary index language are well-formed plain inputs. -/
lemma validPlain_of_mem_unaryIdx {p : ℕ → ℕ → Prop} {y : List Bool}
    (h : y ∈ {y : List Bool | ∃ n i, y = pairEncode (List.replicate n true) (Nat.bits i) ∧
      p n i}) : ValidPlain y := by
  obtain ⟨n, i, rfl, -⟩ := h
  exact ⟨n, _, rfl, canon_bits i⟩

/-! ## From unary-logspace to implicitly logspace computable -/

open Classical in
/-- The extension of `g` to all inputs: `g |x|` on `x = 1^{|x|}`, `[]` elsewhere. -/
noncomputable def unaryExt (g : ℕ → List Bool) (x : List Bool) : List Bool :=
  if x = List.replicate x.length true then g x.length else []

/-- On `1ⁿ` the extension is `g n`. -/
@[simp] lemma unaryExt_replicate (g : ℕ → List Bool) (n : ℕ) :
    unaryExt g (List.replicate n true) = g n := by
  simp [unaryExt]

/-- The index languages of the extension are those of `g`. -/
lemma indexLang_unaryExt (p : List Bool → ℕ → Prop)
    (hp : ∀ x i, p x i ↔ (x = List.replicate x.length true ∧ p x i))
    (q : ℕ → ℕ → Prop) (hq : ∀ n i, p (List.replicate n true) i ↔ q n i) :
    indexLang p =
      {y : List Bool | ∃ n i, y = pairEncode (List.replicate n true) (Nat.bits i) ∧ q n i} := by
  ext y
  constructor
  · rintro ⟨x, i, rfl, h⟩
    obtain ⟨hx, h⟩ := (hp x i).mp h
    refine ⟨x.length, i, by rw [← hx], ?_⟩
    rw [← hq, ← hx]; exact h
  · rintro ⟨n, i, rfl, h⟩
    exact ⟨_, i, rfl, (hq n i).mpr h⟩

/-- **Unary-logspace sequences of polynomial length give implicitly logspace computable
functions** [AB09, Def 4.16]: `unaryExt g`.

**Proof sketch.** Off unary inputs the extension is empty, so its bit and length languages
are exactly `uBit g` and `uLen g` (`indexLang_unaryExt`). -/
theorem UnaryLogspace.implicitlyLogspaceComputable {g : ℕ → List Bool} (h : UnaryLogspace g)
    (hlen : ∃ C c : ℕ, ∀ n, (g n).length ≤ C * (n + 1) ^ c) :
    ImplicitlyLogspaceComputable (unaryExt g) := by
  obtain ⟨C, c, hC⟩ := hlen
  refine ⟨⟨C, c, fun x => ?_⟩, ?_, ?_⟩
  · unfold unaryExt; split_ifs
    · exact hC _
    · simp
  · rw [indexLang_unaryExt _ (fun x i => by
        unfold unaryExt; split_ifs with hx
        · exact ⟨fun h => ⟨hx, h⟩, And.right⟩
        · simp [hx])
      (fun n i => (g n).getD i false = true) (fun n i => by simp)]
    exact h.1
  · rw [indexLang_unaryExt _ (fun x i => by
        unfold unaryExt; split_ifs with hx
        · exact ⟨fun h => ⟨hx, h⟩, And.right⟩
        · simp [hx])
      (fun n i => i < (g n).length) (fun n i => by simp)]
    exact h.2

/-! ## The identity `n ↦ 1ⁿ` -/

namespace LogProg

/-- A `unaryFst` call with one argument `r` on `⟨1ⁿ, w⟩` asks about `⟨1ⁿ, bits (v r)⟩`. -/
lemma astep_call₁ {m d : ℕ} {Λ : Type} (A : ARM m d Λ) (o : Fin d → List Bool → Bool)
    {l l₁ l₀ : Λ} {j : Fin d} {r : Fin m} (hl : A l = .call j .unaryFst [r] l₁ l₀) (n : ℕ)
    (w : List Bool) (v : Fin m → ℕ) :
    astep A o (pairEncode (List.replicate n true) w) (some l, v, none) =
      (some (if o j (pairEncode (List.replicate n true) (Nat.bits (v r))) then l₁ else l₀),
        v, none) := by
  simp only [astep, hl]
  rw [vword_unary₁]

end LogProg

/-- The inputs `⟨1ⁿ, bits i⟩` with `i < n`. -/
def ltLang : Language Bool :=
  {y | ∃ n i, y = pairEncode (List.replicate n true) (Nat.bits i) ∧ i < n}

namespace LtM

/-- The labels of the comparison machine. -/
inductive Lb where
  | start | test | cmp | i1 | i2 | i3 | yes | no
  deriving DecidableEq, Fintype

/-- **The comparison machine**: registers `k` (`0`) and `g = 2k` (`1`); at `test` ask
`dblLang` whether `g = 2n` (then answer `0`), at `cmp` whether `k = i` (then answer `1`),
else increment `k` once and `g` twice. -/
def A : ARM 2 1 Lb
  | .start => .valP 0 .test
  | .test => .call 0 .unaryFst [1] .no .cmp
  | .cmp => .jeqIn 0 .yes .i1
  | .i1 => .inc 0 .i2
  | .i2 => .inc 1 .i3
  | .i3 => .inc 1 .test
  | .yes => .ret true
  | .no => .ret false

/-- Two register values. -/
def vv (a b : ℕ) : Fin 2 → ℕ := fun j => if j = 0 then a else b

/-- Reading register `k`. -/
@[simp] lemma vv_0 (a b : ℕ) : vv a b 0 = a := rfl
/-- Reading register `g`. -/
@[simp] lemma vv_1 (a b : ℕ) : vv a b 1 = b := rfl

/-- Writing register `k`. -/
lemma upd_0 (a b c : ℕ) : Function.update (vv a b) 0 c = vv c b := by
  funext j; fin_cases j <;> simp [vv]

/-- Writing register `g`. -/
lemma upd_1 (a b c : ℕ) : Function.update (vv a b) 1 c = vv a c := by
  funext j; fin_cases j <;> simp [vv]

/-- The oracle: membership in `dblLang`. -/
noncomputable def orc : Fin 1 → List Bool → Bool :=
  fun _ V => MultiTapeTM.indicator (dblLang : Set (List Bool)) V

/-- The base decider answers whether `v = 2n`. -/
lemma orc_eq (n v : ℕ) : orc 0 (pairEncode (List.replicate n true) (Nat.bits v)) =
    decide (v = 2 * n) := by
  rw [orc, indicator_eq_decide]
  refine decide_eq_decide.mpr ⟨fun ⟨n', h⟩ => ?_, fun h => ⟨n, by rw [h]⟩⟩
  obtain ⟨rfl, hb⟩ := pairEncode_replicate_inj h
  exact bits_injective hb

/-- The invariant: syntactic preconditions and registers at most `2 (|y| + 1)`. -/
def G (y : List Bool) (a : AConf 2 Lb) : Prop :=
  PreS A y a ∧ ∀ r, a.2.1 r ≤ 2 * (y.length + 1) ^ 1

/-- **The loop**: from `test` with `k ≤ n`, `k ≤ i`, `g = 2k`, the machine answers `i < n`.

**Proof sketch.** Induction on `n - k`: if `k = n` the base decider says `2k = 2n` and the
machine answers `0` (correct, as `i ≥ k = n`); otherwise if `k = i` it answers `1` (`i < n`);
otherwise it moves to `k + 1`. -/
lemma loop (n i : ℕ) : ∀ d k, k + d = n → k ≤ i →
    AHalt A orc (pairEncode (List.replicate n true) (Nat.bits i)) (G (pairEncode
      (List.replicate n true) (Nat.bits i))) (some .test, vv k (2 * k), none) (decide (i < n)) := by
  set y := pairEncode (List.replicate n true) (Nat.bits i) with hy
  have hl : y.length = 2 * n + 2 + (Nat.bits i).length := by
    simp [hy, pairEncode_eq_dbl, dbl_replicate]; omega
  have hval : ValidPlain y := ⟨n, _, rfl, canon_bits i⟩
  have hG : ∀ (l : Lb) (a b : ℕ), a ≤ n + 1 → b ≤ 2 * n + 2 → G y (some l, vv a b, none) := by
    intro l a b ha hb
    refine ⟨?_, fun r => ?_⟩
    · cases l <;> simp [PreS, A, hval]
    · fin_cases r <;> simp <;> omega
  intro d
  induction d with
  | zero =>
    intro k hk hki
    obtain rfl : k = n := by omega
    refine AHalt.step (hG _ _ _ (by omega) (by omega)) ?_
    rw [astep_call₁ A orc (show A .test = _ from rfl), orc_eq]
    have hf : decide (i < k) = false := by simp; omega
    simp only [vv_1, decide_true, ↓reduceIte, hf]
    exact AHalt.ret rfl (hG _ _ _ (by omega) (by omega))
  | succ d ih =>
    intro k hk hki
    refine AHalt.step (hG _ _ _ (by omega) (by omega)) ?_
    rw [astep_call₁ A orc (show A .test = _ from rfl), orc_eq]
    simp only [vv_1, show 2 * k ≠ 2 * n by omega, decide_false, Bool.false_eq_true, ↓reduceIte]
    refine AHalt.step (hG _ _ _ (by omega) (by omega)) ?_
    by_cases hki' : k = i
    · subst hki'
      have : astep A orc y (some .cmp, vv k (2 * k), none) = (some .yes, vv k (2 * k), none) := by
        simp [astep, A, hy, plainWord_pairEncode]
      rw [this]
      have hlt : decide (k < n) = true := by simp; omega
      rw [hlt]
      exact AHalt.ret rfl (hG _ _ _ (by omega) (by omega))
    · have : astep A orc y (some .cmp, vv k (2 * k), none) = (some .i1, vv k (2 * k), none) := by
        simp [astep, A, hy, plainWord_pairEncode, bits_injective.eq_iff, hki']
      rw [this]
      refine AHalt.step (hG _ _ _ (by omega) (by omega)) ?_
      simp only [astep, A, vv_0, upd_0]
      refine AHalt.step (hG _ _ _ (by omega) (by omega)) ?_
      simp only [astep, A, vv_1, upd_1]
      refine AHalt.step (hG _ _ _ (by omega) (by omega)) ?_
      simp only [astep, A, vv_1, upd_1]
      have := ih (k + 1) (by omega) (by omega)
      rwa [show 2 * k + 1 + 1 = 2 * (k + 1) by ring]

end LtM

open LtM in
/-- **`ltLang` is in `L`**: the comparison machine decides it with the base decider
`dblLang`.

**Proof sketch.** `arm_decides_poly`: on a malformed input the format check rejects; on
`⟨1ⁿ, bits i⟩` the loop (`LtM.loop`) answers `i < n` with registers at most `2n + 2`. -/
theorem ltLang_mem : ltLang ∈ LOGSPACE := by
  refine arm_decides_poly A .start (fun _ => dblLang) (fun _ => dblLang_mem) 2 1 fun y => ?_
  by_cases hv : ValidPlain y
  · obtain ⟨n, w, rfl, hw⟩ := hv
    rw [canon_eq_bits w hw]
    set i := bitsVal w
    have hind : MultiTapeTM.indicator (ltLang : Set (List Bool))
        (pairEncode (List.replicate n true) (Nat.bits i)) = decide (i < n) := by
      rw [indicator_eq_decide]; exact decide_eq_decide.mpr (mem_unaryIdx _ n i)
    rw [hind]
    have hval : ValidPlain (pairEncode (List.replicate n true) (Nat.bits i)) :=
      ⟨n, _, rfl, canon_bits i⟩
    change AHalt A orc _ (G _) _ _
    rw [show (fun _ => 0 : Fin 2 → ℕ) = vv 0 (2 * 0) from by funext j; fin_cases j <;> rfl]
    refine AHalt.step ⟨by simp [PreS, A], fun r => by fin_cases r <;> simp⟩ ?_
    have : astep A orc (pairEncode (List.replicate n true) (Nat.bits i))
        (some .start, vv 0 (2 * 0), none) = (some .test, vv 0 (2 * 0), none) := by
      simp [astep, A, hval]
    rw [this]
    exact loop n i n 0 (by omega) (Nat.zero_le _)
  · have hn : MultiTapeTM.indicator (ltLang : Set (List Bool)) y = false := by
      rw [indicator_eq_decide]
      simp only [decide_eq_false_iff_not]
      exact fun h => hv (validPlain_of_mem_unaryIdx h)
    rw [hn]
    refine ⟨1, ?_, ?_, fun t ht => ?_⟩
    · simp [arun, astep, A, hv]
    · simp [arun, astep, A, hv]
    · obtain rfl : t = 0 := by omega
      exact ⟨by simp [arun, PreS, A], fun r => by simp [arun]⟩

/-- **`n ↦ 1ⁿ` is unary-logspace**: both its languages are `ltLang`. -/
theorem unaryLogspace_replicate : UnaryLogspace fun n => List.replicate n true := by
  have e1 : uBit (fun n => List.replicate n true) = ltLang := by
    ext y; simp only [uBit, ltLang]
    refine exists_congr fun n => exists_congr fun i => and_congr_right fun _ => ?_
    by_cases h : i < n <;> simp [List.getD_eq_getElem?_getD, h]
  have e2 : uLen (fun n => List.replicate n true) = ltLang := by
    ext y; simp [uLen, ltLang]
  exact ⟨e1 ▸ ltLang_mem, e2 ▸ ltLang_mem⟩

end Complexity
