/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.SecureComputation.Garbling.Probability
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.List.GetD
import Mathlib.Tactic.Ring

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Uniform key and row-coin blocks

## Main definitions

This module adds no definitions.

## Main results

* `GarblingProbability.pushesUniform_key_row_blocks`: the key and row-coin blocks used
  by Yao have a uniform joint law, including zero-length blocks.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, §6.2.3, Claim 159.a.
-/

namespace TCSlib.Cryptography.SecureComputation.GarblingProbability

open TCSlib.Cryptography

/-- For `len ≤ 2`, the binary fold `a₀ + 2(a₁ + 2(⋯))` is below four and injective:
`(∀ a, (List.ofFn a).foldr (fun b k => b.toNat + 2*k) 0 < 4) ∧
  Function.Injective (fun a => (List.ofFn a).foldr (fun b k => b.toNat + 2*k) 0)`. -/
theorem assignmentFold_small (len : ℕ) (hlen : len ≤ 2) :
    (∀ a : Fin len → Bool, (List.ofFn a).foldr (fun b k => b.toNat + 2 * k) 0 < 4) ∧
      Function.Injective (fun a : Fin len → Bool =>
        (List.ofFn a).foldr (fun b k => b.toNat + 2 * k) 0) := by
  interval_cases len <;> decide

/-- Selecting distinct blocks of `n` bits preserves the uniform law:
`r ↦ (fun i t => (List.ofFn r).getD (c i * n + t) false)` pushes uniform to uniform,
for an injection `c : I → Fin B` and any unused tail of length `tail`.

**Proof sketch.** The product equivalence embeds a block and its bit into `Fin (B*n)`.
Compose this injection with the inclusion into the raw coin space and restrict its uniform
bit table. Currying the restricted table gives the claimed family of independent blocks. -/
theorem pushesUniform_bits_of_blocks {I : Type} [Fintype I] [DecidableEq I]
    {B n tail : ℕ} (c : I → Fin B) (hinj : Function.Injective c) :
    HardcoreBit.PushesUniform (fun r : Fin (B * n + tail) → Bool =>
      fun i (t : Fin n) => (List.ofFn r).getD ((c i : ℕ) * n + t) false) := by
  let select : I × Fin n → Fin (B * n + tail) :=
    fun p => Fin.castAdd tail (finProdFinEquiv (c p.1, p.2))
  have hselect : Function.Injective select := by
    intro x y hxy
    have hp : (c x.1, x.2) = (c y.1, y.2) := by
      apply (finProdFinEquiv (m := B) (n := n)).injective
      apply Fin.castAdd_injective (B * n) tail
      exact hxy
    apply Prod.ext
    · exact hinj (congrArg (fun p : Fin B × Fin n => p.1) hp)
    · exact congrArg (fun p : Fin B × Fin n => p.2) hp
  have h := (HardcoreBit.pushesUniform_restrict (O := Bool) hselect).comp
    (HardcoreBit.pushesUniform_equiv (Equiv.curry I (Fin n) Bool))
  convert h using 1
  funext r i t
  have heq : (select (i, t) : ℕ) = (c i : ℕ) * n + t := by
    simp only [select, Fin.coe_castAdd, finProdFinEquiv_apply_val]
    ring
  rw [← heq, List.getD_eq_getElem _ _ (by simp only [List.length_ofFn]; exact (select (i, t)).isLt),
    List.getElem_ofFn]
  rfl

/-- Key blocks `b*S+v` and row-half blocks `2*S+2*(4*i+idx i a)+b` are distinct and below
`10*S`, if `V,G ≤ S` and each `idx i` is an injection into `{0,1,2,3}`.

**Proof sketch.** Key indices are below `2*S`; row indices start there. Within keys, the
bit separates the two intervals. Within rows, bounds on the half-bit and assignment index
recover first the gate, then the assignment, then the half-bit. -/
theorem key_row_blocks_injective {S V G : ℕ} (hV : V ≤ S) (hG : G ≤ S)
    {A : Fin G → Type} (idx : (i : Fin G) → A i → ℕ)
    (hidx : ∀ i a, idx i a < 4) (hinj : ∀ i, Function.Injective (idx i)) :
    let c : (Fin V × Bool) ⊕ ((Σ i, A i) × Bool) → ℕ :=
      Sum.elim (fun p => p.2.toNat * S + p.1)
        (fun p => 2 * S + (4 * p.1.1 + idx p.1.1 p.1.2) * 2 + p.2.toNat)
    (∀ p, c p < 10 * S) ∧ Function.Injective c := by
  dsimp only
  have hb (b : Bool) : b.toNat ≤ 1 := by cases b <;> decide
  have hk (p : Fin V × Bool) : p.2.toNat * S + p.1 < 2 * S := by
    have hm := Nat.mul_le_mul_right S (hb p.2)
    have hv := p.1.isLt
    simp only [Nat.one_mul] at hm
    omega
  constructor
  · intro p
    cases p with
    | inl p =>
      simp only [Sum.elim_inl]
      have hh := hk p
      omega
    | inr p =>
      simp only [Sum.elim_inr]
      have hi := p.1.1.isLt
      have ha := hidx p.1.1 p.1.2
      have hh := hb p.2
      omega
  · intro x y hxy
    cases x with
    | inl x =>
      cases y with
      | inl y =>
        obtain ⟨x, b⟩ := x
        obtain ⟨y, c⟩ := y
        have hx := x.isLt
        have hy := y.isLt
        change b.toNat * S + x.val = c.toNat * S + y.val at hxy
        have hbc : b = c := by
          cases b <;> cases c <;> simp_all only [Bool.toNat_false, Bool.toNat_true,
            Nat.zero_mul, Nat.one_mul] <;> omega
        subst c
        have hval : x.val = y.val := Nat.add_left_cancel hxy
        exact congrArg Sum.inl (Prod.ext (Fin.ext hval) rfl)
      | inr y =>
        have hx := hk x
        simp only [Sum.elim_inl, Sum.elim_inr] at hxy
        omega
    | inr x =>
      cases y with
      | inl y =>
        have hy := hk y
        simp only [Sum.elim_inl, Sum.elim_inr] at hxy
        omega
      | inr y =>
        obtain ⟨⟨i, a⟩, b⟩ := x
        obtain ⟨⟨j, a'⟩, c⟩ := y
        have ha := hidx i a
        have ha' := hidx j a'
        have hbit := hb b
        have hbit' := hb c
        simp only [Sum.elim_inr] at hxy
        have hij : i = j := Fin.ext (by omega)
        subst j
        have haa : a = a' := hinj i (by omega)
        subst a'
        have hbc : b = c := by cases b <;> cases c <;> simp_all
        subst c
        rfl

/-- The joint key/row-coin law of Yao's block layout is uniform. For `V,G ≤ S`, row index
injections `idx i : A i → {0,1,2,3}`, and uniform `10*S*n+2*S` bits, the keys read at
`(b*S+v)*n` and the two row halves read at `2*S*n+(4*i+idx i a)*(2*n)` and that offset
plus `n` form independent uniform tables. [PS10, §6.2.3, Claim 159.a]

**Proof sketch.** Embed key blocks and row-half blocks into `Fin (10*S)` using their
intervals, and restrict the raw uniform bit table to those blocks. Split the sum of the
key and row indices. Curry the key indices, curry the row-half indices, turn each pair
of Boolean-indexed row halves into a product, and curry the dependent row index. All
these maps are equivalences, so the joint uniform law is preserved. -/
theorem pushesUniform_key_row_blocks {S V G n : ℕ} (hV : V ≤ S) (hG : G ≤ S)
    {A : Fin G → Type} [∀ i, Fintype (A i)] [∀ i, DecidableEq (A i)]
    (idx : (i : Fin G) → A i → ℕ) (hidx : ∀ i a, idx i a < 4)
    (hinj : ∀ i, Function.Injective (idx i)) :
    HardcoreBit.PushesUniform (fun r : Fin (10 * S * n + 2 * S) → Bool =>
      ((fun (v : Fin V) (b : Bool) (t : Fin n) =>
          (List.ofFn r).getD ((b.toNat * S + v) * n + t) false),
        fun i a =>
          ((fun t : Fin n =>
            (List.ofFn r).getD (2 * S * n + (4 * i + idx i a) * (2 * n) + t) false),
           (fun t : Fin n =>
            (List.ofFn r).getD (2 * S * n + (4 * i + idx i a) * (2 * n) + n + t)
              false)))) := by
  classical
  let K := Fin n → Bool
  let I := (Fin V × Bool) ⊕ ((Σ i, A i) × Bool)
  let c : I → ℕ := Sum.elim (fun p => p.2.toNat * S + p.1)
    (fun p => 2 * S + (4 * p.1.1 + idx p.1.1 p.1.2) * 2 + p.2.toNat)
  have hc := key_row_blocks_injective hV hG idx hidx hinj
  let c' : I → Fin (10 * S) := fun p => ⟨c p, hc.1 p⟩
  have hc' : Function.Injective c' := fun x y h => hc.2 (congrArg Fin.val h)
  let eK : (Fin V × Bool → K) ≃ (Fin V → Bool → K) := Equiv.curry _ _ _
  let eR : ((Σ i, A i) × Bool → K) ≃ ((i : Fin G) → A i → K × K) :=
    (Equiv.curry _ _ _).trans ((Equiv.piCongrRight fun _ =>
      Equiv.boolArrowEquivProd K).trans (Equiv.piCurry fun i (_ : A i) => K × K))
  have h := (pushesUniform_bits_of_blocks (n := n) (tail := 2 * S) c' hc').comp
    ((HardcoreBit.pushesUniform_equiv
      (Equiv.sumArrowEquivProdArrow (Fin V × Bool) ((Σ i, A i) × Bool) K)).comp
      (HardcoreBit.pushesUniform_equiv (eK.prodCongr eR)))
  convert h using 1
  funext r
  apply Prod.ext
  · rfl
  · funext i a
    apply Prod.ext <;> funext t
    · change (List.ofFn _).getD
        (2 * S * n + (4 * i + idx i a) * (2 * n) + t) false =
          (List.ofFn _).getD ((2 * S + (4 * i + idx i a) * 2 + 0) * n + t) false
      congr 1; ring
    · change (List.ofFn _).getD
        (2 * S * n + (4 * i + idx i a) * (2 * n) + n + t) false =
          (List.ofFn _).getD ((2 * S + (4 * i + idx i a) * 2 + 1) * n + t) false
      congr 1; ring

end TCSlib.Cryptography.SecureComputation.GarblingProbability
