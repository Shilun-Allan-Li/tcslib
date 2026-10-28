/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.Asymptotic.HardCoreClaims

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Hard-core bits for one-way permutations: the balanced Goldreich–Levin permutation

[PS10, §3.4] states its purpose as "the existence of OWPs implies the existence of OWPs with a
hard-core bit" (p. 86), from which [PS10, Theorem 79.4] builds a pseudorandom generator from
any one-way permutation (p. 84) and Chapter 4 builds commitment schemes
[PS10, Theorem 126.4]. Goldreich–Levin [PS10, Theorem 87.3] (`goldreich_levin`) provides
`g(x, r) = (f(x), r)` with `|x| = |r|`: a permutation of `{0,1}^{2n}` — a family defined at
*even* lengths only, with the typed input length `var + var` (`FunFamily.glPad`), which can
never be packaged as the `PermFamily` (one permutation of `{0,1}^n` for *every* `n`) that
`OneWayPermutation` and the consumers `owp_hardcore_prg`, `cor_81_7`, `owp_commitment`,
`exists_commitment_of_owp_hardCore` and `zk_proof_of_owp_levinReduction` take (run-3 audit,
finding P4-1: `glPad`'s input length is the syntactic polynomial `var + var ≠ var`).

This file closes the gap with the **balanced** Goldreich–Levin permutation
`PermFamily.glHalf`: at length `n` write `m := ⌊n/2⌋` and
`g_n(x ‖ w) := f_m(x) ‖ w` for `x ∈ {0,1}^m`, `w ∈ {0,1}^{n − m}` — the first `m` bits go
through `f_m`, the remaining `n − m` bits (`r`, plus one pass-through bit when `n` is odd) are
copied; the hard-core bit is `glHalfBit n (x ‖ w) := ⟨x, w|_m⟩`, the inner product of the
first two blocks of `m` bits. At even `n = m + m` this is literally `FunFamily.glPad` of `f`
at parameter `m` (`PermFamily.glHalf_f_even`, `glHalfBit_even`); at odd `n = m + m + 1` it is
`glPad` at `m` followed by an untouched bit (`PermFamily.glHalf_f_odd`, `glHalfBit_odd`), and
the prediction and inversion experiments at `n` are those of `glPad` at `m` with the extra
bit turned into a coin of the adversary (`predProb_glHalf_even`, `predProb_glHalf_odd`,
`invProb_glHalf_even`, `invProb_glHalf_odd_le`). The theorem `OneWayPermutation.glHalf` —
`f` a one-way permutation ⇒ `glHalf f` a one-way permutation with hard-core bit `glHalfBit` —
is the "(OWP)" clause of [PS10, Theorem 87.3] in the form every consumer needs;
`exists_owp_hardCore` and `exists_securePRG_of_owp` are the textbook consequences.

**Deviation:** the text's `g` is defined on `{0,1}^{2n}` only ("`|x| = |r|`"); `glHalf` is its
extension to every length by one pass-through bit at odd lengths, so that it is a
`PermFamily` (domain exactly `{0,1}^n` at every `n`, the frozen shape of DESIGN §2.9). The
pass-through bit is uniform and independent of `x`, so it costs nothing: one-wayness and the
hard-core property at `2m + 1` reduce to those of `glPad` at `m`.

## Main definitions

* `TCSlib.Cryptography.PermFamily.glHalf` — the balanced Goldreich–Levin permutation
  `x ‖ w ↦ f_{⌊n/2⌋}(x) ‖ w` (with `PermFamily.glHalfFun`, `PermFamily.glHalfInv`).
* `TCSlib.Cryptography.glHalfBit` — its hard-core bit `⟨x, w|_{⌊n/2⌋}⟩`.

## Main results

* `TCSlib.Cryptography.OneWayPermutation.glHalf` [PS10, Theorem 87.3, "(OWP)" clause]: a
  one-way permutation yields a one-way permutation with a hard-core bit (sorried under its
  sketch; the fill routes through `FunFamily.StrongOneWay.glPad` and
  `FunFamily.StrongOneWay.glPad_hardCore` at parameter `⌊n/2⌋`).
* `TCSlib.Cryptography.exists_owp_hardCore`, `TCSlib.Cryptography.exists_securePRG_of_owp`
  [PS10, §3.4, pp. 84 and 86]: the hypothesis of Theorems 79.4, 81.7 and 126.4 from one-way
  permutations alone; pseudorandom generators from one-way permutations.
* The proved bridges `PermFamily.glHalf_f_even`, `PermFamily.glHalf_f_odd`, `glHalfBit_even`,
  `glHalfBit_odd`, `predProb_glHalf_even`, `predProb_glHalf_odd`, `invProb_glHalf_even`,
  `invProb_glHalf_odd_le`, and `Negligible.comp_div_two` (negligible in `⌊n/2⌋` is negligible
  in `n`).

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (§3.3.4: Theorem 79.4; §3.3.5: Corollary 81.7; §3.4: pp. 84, 86; §3.4.2: Theorem 87.3;
  §4.7: Theorem 126.4.)
* [Gar26] S. Garg, *A Course in Theory of Cryptography*, lecture notes, UC Berkeley,
  draft of 22 January 2026, §2.5 (Theorem 2.3), §3.3 (Theorem 3.2).
* [GL89] O. Goldreich, L. Levin, *A hard-core predicate for all one-way functions*, STOC 1989.
-/

namespace TCSlib.Cryptography

open Complexity Turing Finset

/-! ## The balanced permutation -/

/-- Transport of a permutation family along an equality of parameters: `P.f k` and `P.f m`
agree under the casts `Fin.cast` when `k = m` (used to pass between `⌊(m + m)/2⌋` and `m`). -/
theorem PermFamily.f_congr (P : PermFamily) {k m : ℕ} (h : k = m) (x : Fin k → Bool)
    (i : Fin k) :
    P.f k x i = P.f m (fun j => x (Fin.cast h.symm j)) (Fin.cast h i) := by
  subst h; rfl

/-- The forward map of the balanced Goldreich–Levin permutation at length `n`: position
`i < ⌊n/2⌋` carries bit `i` of `f_{⌊n/2⌋}` applied to the first `⌊n/2⌋` bits of the input, every
other position is copied. -/
def PermFamily.glHalfFun (P : PermFamily) (n : ℕ) (z : Fin n → Bool) (i : Fin n) : Bool :=
  if h : (i : ℕ) < n / 2 then
    P.f (n / 2) (fun j => z (Fin.castLE (Nat.div_le_self n 2) j)) ⟨i, h⟩
  else z i

/-- The inverse map of the balanced Goldreich–Levin permutation: `f_{⌊n/2⌋}⁻¹` on the first
`⌊n/2⌋` bits, the identity elsewhere. -/
def PermFamily.glHalfInv (P : PermFamily) (n : ℕ) (z : Fin n → Bool) (i : Fin n) : Bool :=
  if h : (i : ℕ) < n / 2 then
    (P.f (n / 2)).symm (fun j => z (Fin.castLE (Nat.div_le_self n 2) j)) ⟨i, h⟩
  else z i

/-- Unfolding of the forward map on the first block: position `j < ⌊n/2⌋` carries bit `j` of
`f_{⌊n/2⌋}(x)` where `x` is the first block of the input. -/
theorem PermFamily.glHalfFun_castLE (P : PermFamily) (n : ℕ) (z : Fin n → Bool)
    (j : Fin (n / 2)) :
    P.glHalfFun n z (Fin.castLE (Nat.div_le_self n 2) j) =
      P.f (n / 2) (fun j => z (Fin.castLE (Nat.div_le_self n 2) j)) j := by
  simp only [PermFamily.glHalfFun, Fin.coe_castLE, j.isLt, dite_true]

/-- Unfolding of the inverse map on the first block. -/
theorem PermFamily.glHalfInv_castLE (P : PermFamily) (n : ℕ) (z : Fin n → Bool)
    (j : Fin (n / 2)) :
    P.glHalfInv n z (Fin.castLE (Nat.div_le_self n 2) j) =
      (P.f (n / 2)).symm (fun j => z (Fin.castLE (Nat.div_le_self n 2) j)) j := by
  simp only [PermFamily.glHalfInv, Fin.coe_castLE, j.isLt, dite_true]

/-- The **balanced Goldreich–Levin permutation** of a permutation family `f`
[PS10, Theorem 87.3, "(OWP)" clause, parametrised by the output length]: at length `n`, with
`m := ⌊n/2⌋`, `g_n(x ‖ w) = f_m(x) ‖ w` for `x ∈ {0,1}^m` and `w ∈ {0,1}^{n − m}` — the text's
`g(x, r) = (f(x), r)` with `|x| = |r| = m` at even `n`, followed by one pass-through bit at
odd `n`. A permutation of `{0,1}^n` at every `n`, hence a `PermFamily` (which
`FunFamily.glPad`, of input length `var + var`, is not; run-3 audit P4-1).

**Deviation:** the text defines `g` on `{0,1}^{2n}` only; the odd lengths are filled by a
pass-through bit so that the family has the frozen `PermFamily` shape. -/
def PermFamily.glHalf (P : PermFamily) : PermFamily where
  f n :=
    { toFun := P.glHalfFun n
      invFun := P.glHalfInv n
      left_inv := fun z => by
        funext i
        by_cases h : (i : ℕ) < n / 2
        · have hfun : (fun j => P.glHalfFun n z (Fin.castLE (Nat.div_le_self n 2) j)) =
              P.f (n / 2) (fun j => z (Fin.castLE (Nat.div_le_self n 2) j)) :=
            funext fun j => P.glHalfFun_castLE n z j
          have : i = Fin.castLE (Nat.div_le_self n 2) ⟨i, h⟩ := Fin.ext rfl
          rw [this, PermFamily.glHalfInv_castLE, hfun, Equiv.symm_apply_apply]
        · simp only [PermFamily.glHalfInv, PermFamily.glHalfFun, h, dite_false]
      right_inv := fun z => by
        funext i
        by_cases h : (i : ℕ) < n / 2
        · have hfun : (fun j => P.glHalfInv n z (Fin.castLE (Nat.div_le_self n 2) j)) =
              (P.f (n / 2)).symm (fun j => z (Fin.castLE (Nat.div_le_self n 2) j)) :=
            funext fun j => P.glHalfInv_castLE n z j
          have : i = Fin.castLE (Nat.div_le_self n 2) ⟨i, h⟩ := Fin.ext rfl
          rw [this, PermFamily.glHalfFun_castLE, hfun, Equiv.apply_symm_apply]
        · simp only [PermFamily.glHalfInv, PermFamily.glHalfFun, h, dite_false] }

/-- Unfolding: `g_n(z)_i = f_{⌊n/2⌋}(z|_{⌊n/2⌋})_i` for `i < ⌊n/2⌋` and `z_i` otherwise. -/
theorem PermFamily.glHalf_f_apply (P : PermFamily) (n : ℕ) (z : Fin n → Bool) (i : Fin n) :
    P.glHalf.f n z i = if h : (i : ℕ) < n / 2 then
      P.f (n / 2) (fun j => z (Fin.castLE (Nat.div_le_self n 2) j)) ⟨i, h⟩ else z i := rfl

/-- The inner product is invariant under transport along an equality of lengths. -/
theorem HardcoreBit.ip_cast {k m : ℕ} (h : k = m) (x r : Fin k → Bool) :
    HardcoreBit.ip x r =
      HardcoreBit.ip (fun j => x (Fin.cast h.symm j)) (fun j => r (Fin.cast h.symm j)) := by
  subst h; rfl

/-- The **hard-core bit of the balanced permutation**: `⟨x, w|_m⟩` with `m = ⌊n/2⌋`, the inner
product of the first block `x` of `m` bits with the following block of `m` bits
(the `r` of [PS10, Theorem 87.3]; the pass-through bit of odd `n` is ignored). It does not
depend on the permutation family. -/
def glHalfBit (n : ℕ) (z : Fin n → Bool) : Bool :=
  HardcoreBit.ip (fun j : Fin (n / 2) => z (Fin.castLE (Nat.div_le_self n 2) j))
    (fun j : Fin (n / 2) => z ⟨n / 2 + j, by omega⟩)

/-! ## Even lengths: the balanced permutation is `glPad` -/

/-- **At even length `m + m` the balanced permutation is the padded family**
`g(x, r) = (f(x), r)` of Goldreich–Levin at parameter `m`: `P.glHalf.f (m + m) = P.toFunFamily.glPad.f m`
as functions on `{0,1}^{m+m}` (`FunFamily.glPad`'s input length `var + var` evaluates to
`m + m`). -/
theorem PermFamily.glHalf_f_even (P : PermFamily) (m : ℕ) (z : Fin (m + m) → Bool) :
    P.glHalf.f (m + m) z = P.toFunFamily.glPad.f m z := by
  have hm : (m + m) / 2 = m := by omega
  funext i
  change P.glHalfFun (m + m) z i =
    Fin.append (P.f m fun j => z (Fin.castAdd m j)) (fun j => z (Fin.natAdd m j)) i
  by_cases h : (i : ℕ) < m
  · have hi : i = Fin.castAdd m ⟨i, h⟩ := Fin.ext rfl
    rw [hi, Fin.append_left]
    simp only [PermFamily.glHalfFun, Fin.coe_castAdd, hm, h, dite_true]
    rw [PermFamily.f_congr P hm]
    rfl
  · have hi : i = Fin.natAdd m ⟨i - m, by omega⟩ := Fin.ext (by simp; omega)
    rw [hi, Fin.append_right]
    simp only [PermFamily.glHalfFun, Fin.coe_natAdd, hm]
    rw [dif_neg (by omega)]

/-- **At even length the hard-core bit is Goldreich–Levin's `⟨x, r⟩`**:
`glHalfBit (m + m) = P.toFunFamily.glBit m` (`FunFamily.glBit`, the inner product of the two
halves). -/
theorem glHalfBit_even (P : PermFamily) (m : ℕ) (z : Fin (m + m) → Bool) :
    glHalfBit (m + m) z = P.toFunFamily.glBit m z := by
  have hm : (m + m) / 2 = m := by omega
  change _ = HardcoreBit.ip (fun j => z (Fin.castAdd m j)) (fun j => z (Fin.natAdd m j))
  unfold glHalfBit
  rw [HardcoreBit.ip_cast hm]
  congr 1
  funext j
  congr 1
  exact Fin.ext (by simp only [Fin.coe_cast, Fin.coe_natAdd]; omega)

/-- **Prediction experiments at even length**: predicting `glHalfBit` from `g_{m+m}` is
predicting `⟨x, r⟩` from `glPad f` at parameter `m` (the concrete `predProb` of
[Gar26, Definition 2.3]). -/
theorem predProb_glHalf_even {ρ : Type*} [Fintype ρ] (P : PermFamily) (m : ℕ)
    (A : (Fin (m + m) → Bool) → ρ → Bool) :
    predProb (P.glHalf.f (m + m)) (glHalfBit (m + m)) A =
      predProb (P.toFunFamily.glPad.f m) (P.toFunFamily.glBit m) A := by
  unfold predProb
  congr 1
  funext z
  rw [PermFamily.glHalf_f_even, glHalfBit_even]

/-- **Inversion experiments at even length**: inverting `g_{m+m}` is inverting `glPad f` at
parameter `m`. -/
theorem invProb_glHalf_even {ρ : Type*} [Fintype ρ] (P : PermFamily) (m : ℕ)
    (A : (Fin (m + m) → Bool) → ρ → (Fin (m + m) → Bool)) :
    invProb (P.glHalf.f (m + m)) A = invProb (P.toFunFamily.glPad.f m) A := by
  unfold invProb
  congr 1
  funext z
  rw [PermFamily.glHalf_f_even, PermFamily.glHalf_f_even]

/-! ## Odd lengths: `glPad` followed by a pass-through bit -/

/-- **At odd length `m + m + 1` the balanced permutation is `glPad` at `m` followed by an
untouched bit**: `g(x ‖ r ‖ e) = (f(x) ‖ r) ‖ e`.

**Proof sketch.** Pointwise, with `⌊(m + m + 1)/2⌋ = m`. A position `i` is either the last
one (both sides give `e`: `Fin.snoc_last`, and the `dite` of `glHalfFun` takes its `else`
branch) or `castSucc j` with `j < m + m` (`Fin.eq_castSucc_or_eq_last`). For `j < m` both sides
are bit `j` of `f_m(x)` (`Fin.append_left`; the first block of `x ‖ r ‖ e` is `x` by
`Fin.snoc_castSucc`, transported along `⌊(m + m + 1)/2⌋ = m` by `PermFamily.f_congr`); for
`m ≤ j` both sides are the copied bit `r_{j − m}` (`Fin.append_right`, `Fin.snoc_castSucc`). -/
theorem PermFamily.glHalf_f_odd (P : PermFamily) (m : ℕ) (z : Fin (m + m) → Bool) (e : Bool) :
    P.glHalf.f (m + m + 1) (Fin.snoc z e) = Fin.snoc (P.toFunFamily.glPad.f m z) e := by
  have hm : (m + m + 1) / 2 = m := by omega
  funext i
  change P.glHalfFun (m + m + 1) (Fin.snoc z e) i =
    (Fin.snoc (Fin.append (P.f m fun j => z (Fin.castAdd m j)) (fun j => z (Fin.natAdd m j))) e :
      Fin (m + m + 1) → Bool) i
  rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
  · rw [Fin.snoc_castSucc]
    by_cases h : (j : ℕ) < m
    · have hj : j = Fin.castAdd m ⟨j, h⟩ := Fin.ext rfl
      rw [hj, Fin.append_left]
      simp only [PermFamily.glHalfFun, Fin.coe_castSucc, Fin.coe_castAdd, hm, h, dite_true]
      rw [PermFamily.f_congr P hm]
      have hx : (fun j' => (Fin.snoc z e : Fin (m + m + 1) → Bool)
          (Fin.castLE (Nat.div_le_self (m + m + 1) 2) (Fin.cast hm.symm j')) : Fin m → Bool) =
          fun j' => z (Fin.castAdd m j') := by
        funext j'
        have : Fin.castLE (Nat.div_le_self (m + m + 1) 2) (Fin.cast hm.symm j') =
            Fin.castSucc (Fin.castAdd m j') := Fin.ext (by simp)
        rw [this, Fin.snoc_castSucc]
      rw [hx]
      rfl
    · have hj : j = Fin.natAdd m ⟨j - m, by omega⟩ := Fin.ext (by simp; omega)
      rw [hj, Fin.append_right]
      simp only [PermFamily.glHalfFun, Fin.coe_castSucc, Fin.coe_natAdd, hm]
      rw [dif_neg (by omega), Fin.snoc_castSucc]
  · rw [Fin.snoc_last]
    simp only [PermFamily.glHalfFun, Fin.val_last, hm]
    rw [dif_neg (by omega), Fin.snoc_last]

/-- **At odd length the hard-core bit ignores the pass-through bit**:
`glHalfBit (m + m + 1) (z ‖ e) = ⟨x, r⟩` for `z = x ‖ r`. -/
theorem glHalfBit_odd (P : PermFamily) (m : ℕ) (z : Fin (m + m) → Bool) (e : Bool) :
    glHalfBit (m + m + 1) (Fin.snoc z e) = P.toFunFamily.glBit m z := by
  have hm : (m + m + 1) / 2 = m := by omega
  change _ = HardcoreBit.ip (fun j => z (Fin.castAdd m j)) (fun j => z (Fin.natAdd m j))
  unfold glHalfBit
  rw [HardcoreBit.ip_cast hm]
  congr 1
  · funext j
    have : Fin.castLE (Nat.div_le_self (m + m + 1) 2) (Fin.cast hm.symm j) =
        Fin.castSucc (Fin.castAdd m j) := Fin.ext (by simp)
    rw [this, Fin.snoc_castSucc]
  · funext j
    have : (⟨(m + m + 1) / 2 + ↑(Fin.cast hm.symm j), by omega⟩ : Fin (m + m + 1)) =
        Fin.castSucc (Fin.natAdd m j) :=
      Fin.ext (by simp only [Fin.coe_cast, Fin.coe_castSucc, Fin.coe_natAdd]; omega)
    rw [this, Fin.snoc_castSucc]

/-- The re-encoding `(z, (e, c)) ↦ (z ‖ e, c)` of the sample spaces of the odd-length
experiments: the pass-through bit `e` of the input becomes a coin of the adversary. -/
private def snocCoins (m : ℕ) (ρ : Type*) :
    (Fin (m + m) → Bool) × (Bool × ρ) ≃ (Fin (m + m + 1) → Bool) × ρ where
  toFun w := (Fin.snoc w.1 w.2.1, w.2.2)
  invFun w := (Fin.init w.1, (w.1 (Fin.last _), w.2))
  left_inv w := by
    obtain ⟨z, e, c⟩ := w
    simp only [Fin.init_snoc, Fin.snoc_last]
  right_inv w := by
    obtain ⟨z, c⟩ := w
    simp only [Fin.snoc_init_self]

/-- **Prediction experiments at odd length**: predicting `glHalfBit` from `g_{m+m+1}` with a
predictor `A` is predicting `⟨x, r⟩` from `glPad f` at parameter `m` with the predictor that
draws the pass-through bit `e` as an extra coin and calls `A` on `(f(x) ‖ r) ‖ e`. -/
theorem predProb_glHalf_odd {ρ : Type*} [Fintype ρ] (P : PermFamily) (m : ℕ)
    (A : (Fin (m + m + 1) → Bool) → ρ → Bool) :
    predProb (P.glHalf.f (m + m + 1)) (glHalfBit (m + m + 1)) A =
      predProb (P.toFunFamily.glPad.f m) (P.toFunFamily.glBit m)
        (fun (y : Fin (m + m) → Bool) (c : Bool × ρ) => A (Fin.snoc y c.1) c.2) := by
  unfold predProb
  refine (uprob_eq_of_equiv (snocCoins m ρ) fun w => ?_).symm
  obtain ⟨z, e, c⟩ := w
  show (A (Fin.snoc (P.toFunFamily.glPad.f m z) e) c = P.toFunFamily.glBit m z) ↔
    (A (P.glHalf.f (m + m + 1) (Fin.snoc z e)) c = glHalfBit (m + m + 1) (Fin.snoc z e))
  rw [PermFamily.glHalf_f_odd, glHalfBit_odd P]

/-- **Inversion experiments at odd length**: an inverter `A` of `g_{m+m+1}` gives the inverter
of `glPad f` at parameter `m` that draws the pass-through bit `e`, calls `A` on `(f(x) ‖ r) ‖ e`
and drops the last bit of the answer; it inverts at least as often (a correct answer of `A`
has the right last bit and a correct `glPad`-preimage in front). -/
theorem invProb_glHalf_odd_le {ρ : Type*} [Fintype ρ] (P : PermFamily) (m : ℕ)
    (A : (Fin (m + m + 1) → Bool) → ρ → (Fin (m + m + 1) → Bool)) :
    invProb (P.glHalf.f (m + m + 1)) A ≤
      invProb (P.toFunFamily.glPad.f m)
        (fun (y : Fin (m + m) → Bool) (c : Bool × ρ) => Fin.init (A (Fin.snoc y c.1) c.2)) := by
  unfold invProb
  rw [← uprob_comp_equiv (snocCoins m ρ)]
  refine uprob_mono fun w hw => ?_
  obtain ⟨z, e, c⟩ := w
  simp only [snocCoins, Equiv.coe_fn_mk, PermFamily.glHalf_f_odd] at hw ⊢
  have hw' : P.glHalf.f (m + m + 1)
      (Fin.snoc (Fin.init (A (Fin.snoc (P.toFunFamily.glPad.f m z) e) c))
        (A (Fin.snoc (P.toFunFamily.glPad.f m z) e) c (Fin.last _))) =
      Fin.snoc (P.toFunFamily.glPad.f m z) e := by
    rwa [Fin.snoc_init_self]
  rw [PermFamily.glHalf_f_odd] at hw'
  have := congrArg Fin.init hw'
  simpa only [Fin.init_snoc] using this

/-! ## Negligible functions of `⌊n/2⌋` -/

/-- **Negligible in `⌊n/2⌋` is negligible in `n`**: if `ν` is negligible then so is
`n ↦ ν(⌊n/2⌋)` (the reductions of `OneWayPermutation.glHalf` run the Goldreich–Levin adversaries
at parameter `⌊n/2⌋`).

**Proof sketch.** Given `c`, take `n₀` with `|ν m| < 1/m^{c+1}` for `m ≥ n₀`. For
`n ≥ 2(n₀ + 3^c + 1)` the value `m := ⌊n/2⌋` satisfies `m ≥ n₀`, `m ≥ 3^c` and `n ≤ 3m`, so
`n^c ≤ 3^c m^c ≤ m^{c+1}` and `|ν m| < 1/m^{c+1} ≤ 1/n^c`. -/
theorem Negligible.comp_div_two {ν : ℕ → ℝ} (hν : Negligible ν) :
    Negligible fun n => ν (n / 2) := by
  intro c
  obtain ⟨n₀, hn₀⟩ := hν (c + 1)
  refine ⟨2 * (n₀ + 3 ^ c + 1), fun n hn => ?_⟩
  have hd : 0 < 3 ^ c := by positivity
  obtain ⟨hm, h3, hpos⟩ : n₀ ≤ n / 2 ∧ 3 ^ c ≤ n / 2 ∧ 0 < n / 2 := by
    generalize 3 ^ c = d at hd hn ⊢
    omega
  refine lt_of_lt_of_le (hn₀ (n / 2) hm) ?_
  have hmR : (0 : ℝ) < ((n / 2 : ℕ) : ℝ) := by exact_mod_cast hpos
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  rw [div_le_div_iff₀ (by positivity) (by positivity), one_mul, one_mul]
  have hle : (n : ℝ) ≤ 3 * ((n / 2 : ℕ) : ℝ) := by
    have : n ≤ 3 * (n / 2) := by omega
    exact_mod_cast this
  calc (n : ℝ) ^ c ≤ (3 * ((n / 2 : ℕ) : ℝ)) ^ c := by gcongr
    _ = (3 : ℝ) ^ c * ((n / 2 : ℕ) : ℝ) ^ c := by rw [_root_.mul_pow]
    _ ≤ ((n / 2 : ℕ) : ℝ) * ((n / 2 : ℕ) : ℝ) ^ c := by
        gcongr
        exact_mod_cast h3
    _ = ((n / 2 : ℕ) : ℝ) ^ (c + 1) := by ring

/-! ## Encodings and machines for the balanced permutation -/

/-- The first `k` bits of an encoded string are the encoding of its restriction. -/
private theorem take_ofFn_castLE {n k : ℕ} (h : k ≤ n) (z : Fin n → Bool) :
    (List.ofFn z).take k = List.ofFn fun j : Fin k => z (Fin.castLE h j) := by
  refine List.ext_getElem (by simp [h]) fun j hj₁ hj₂ => ?_
  simp only [List.getElem_take, List.getElem_ofFn]
  rfl

/-- The `k` bits after the first `a` of an encoded string. -/
private theorem take_drop_ofFn {n a k : ℕ} (h : a + k ≤ n) (z : Fin n → Bool) :
    ((List.ofFn z).drop a).take k = List.ofFn fun j : Fin k => z ⟨a + j, by omega⟩ := by
  refine List.ext_getElem (by simp; omega) fun j hj₁ hj₂ => ?_
  simp only [List.getElem_take, List.getElem_drop, List.getElem_ofFn]

/-- **The encoding of `g_n(z)`**: `f_{⌊n/2⌋}` of the first block followed by the remaining bits
of `z`. -/
theorem PermFamily.ofFn_glHalf_f (P : PermFamily) (n : ℕ) (z : Fin n → Bool) :
    List.ofFn (P.glHalf.f n z) =
      List.ofFn (P.f (n / 2) fun j => z (Fin.castLE (Nat.div_le_self n 2) j)) ++
        (List.ofFn z).drop (n / 2) := by
  refine List.ext_getElem ?_ fun j hj₁ hj₂ => ?_
  · simp only [List.length_ofFn, List.length_append, List.length_drop]
    omega
  simp only [List.length_ofFn] at hj₁
  rw [List.getElem_ofFn, PermFamily.glHalf_f_apply]
  by_cases h : j < n / 2
  · rw [dif_pos h, List.getElem_append_left (by simp [h]), List.getElem_ofFn]
  · rw [dif_neg h, List.getElem_append_right (by simp; omega), List.getElem_drop, List.getElem_ofFn]
    congr 1
    exact Fin.ext (by simp; omega)

/-- **The balanced permutation is easy to compute** from an evaluator `F` of `f` on `⟨1^n, x⟩`:
on `⟨1^n, z⟩` halve the parameter (`unaryHalf`), cut `z` after `⌊n/2⌋` bits, apply `F` to the
first block at parameter `⌊n/2⌋` and copy the rest. -/
theorem PermFamily.glHalf_easy (P : PermFamily) {F : List Bool → List Bool}
    (hF : PolyTimeComputable F)
    (hFx : ∀ n (x : Fin n → Bool), F (NUPPT.advInput n (List.ofFn x)) = List.ofFn (P.f n x)) :
    P.glHalf.toFunFamily.Easy := by
  have huh : PolyTimeComputable fun w => unaryHalf (pairFstD w) :=
    ptcComp unaryHalf_poly polyTimeComputable_pairFstD
  refine ⟨fun w => F (pairEncode (unaryHalf (pairFstD w))
      ((pairSndD w).take (unaryHalf (pairFstD w)).length)) ++
      (pairSndD w).drop (unaryHalf (pairFstD w)).length,
    (ptcComp hF (huh.pairEncode (takeLen_poly huh polyTimeComputable_pairSndD))).append
      (dropLen_poly huh polyTimeComputable_pairSndD), fun n z => ?_⟩
  have hFx' : ∀ n (x : Fin n → Bool),
      F (pairEncode (List.replicate n true) (List.ofFn x)) = List.ofFn (P.f n x) := hFx
  simp only [NUPPT.advInput, pairFstD_pairEncode, pairSndD_pairEncode, unaryHalf,
    List.length_replicate]
  rw [take_ofFn_castLE (Nat.div_le_self n 2), hFx', PermFamily.toFunFamily_f]
  exact (P.ofFn_glHalf_f n z).symm

/-- **The hard-core bit of the balanced permutation is easy to compute**: on `⟨1^n, z⟩` halve
the parameter, cut the two blocks of `⌊n/2⌋` bits and apply the inner-product evaluator
`ipFun`. -/
theorem glHalfBit_easy : ∃ H : List Bool → List Bool, PolyTimeComputable H ∧
    ∀ n (z : Fin n → Bool), H (NUPPT.advInput n (List.ofFn z)) = [glHalfBit n z] := by
  have huh : PolyTimeComputable fun w => unaryHalf (pairFstD w) :=
    ptcComp unaryHalf_poly polyTimeComputable_pairFstD
  refine ⟨fun w => ipFun (pairEncode ((pairSndD w).take (unaryHalf (pairFstD w)).length)
      (((pairSndD w).drop (unaryHalf (pairFstD w)).length).take (unaryHalf (pairFstD w)).length)),
    ptcComp ipFun_poly ((takeLen_poly huh polyTimeComputable_pairSndD).pairEncode
      (takeLen_poly huh (dropLen_poly huh polyTimeComputable_pairSndD))), fun n z => ?_⟩
  simp only [NUPPT.advInput, pairFstD_pairEncode, pairSndD_pairEncode, unaryHalf,
    List.length_replicate]
  rw [take_ofFn_castLE (Nat.div_le_self n 2), take_drop_ofFn (by omega), ipFun_ofFn]
  rfl

/-- The post-processing of the odd-length inverter: the answer truncated to the length of the
argument `y` (dropping the pass-through bit). -/
private def glHalfInvPost (v : List Bool) : List Bool :=
  (pairSndD v).take (NUPPT.inArg (pairFstD v)).length

/-- The post-processing of the odd-length inverter is polynomial-time. -/
private theorem glHalfInvPost_poly : PolyTimeComputable glHalfInvPost :=
  takeLen_poly (NUPPT.polyTimeComputable_inArg.comp polyTimeComputable_pairFstD)
    polyTimeComputable_pairSndD

/-- The parameter `2m + 1` as a syntactic polynomial. -/
private def oddParam : PolyExpr := .add (.add .var .var) (.const 1)

/-- **The odd-length inverter**: for an inverter `A` of `glHalf` and the parameter `m`, the
machine at parameter `m` that draws one coin `e`, runs `A` at parameter `2m + 1` on `y ++ [e]`
and drops the last bit of the answer (`Complexity.NUPPT.reparam` and `NUPPT.wrap`). -/
noncomputable def glHalfOddInv (A : NUPPT) : NUPPT :=
  (A.reparam oddParam).wrap owpPredPre_poly glHalfInvPost_poly (fun _ => []) (.const 0)
    (fun _ => by simp) (.const 1)

/-- **The odd-length predictor**: for a predictor `A` of `glHalfBit` and the parameter `m`, the
machine at parameter `m` that draws one coin `e`, runs `A` at parameter `2m + 1` on `y ++ [e]`
and returns its verdict. -/
noncomputable def glHalfOddPred (A : NUPPT) : NUPPT :=
  (A.reparam oddParam).wrap owpPredPre_poly polyTimeComputable_pairSndD (fun _ => []) (.const 0)
    (fun _ => by simp) (.const 1)

/-- The coins `(e, c)` of the odd-length machines (for any post-processing `post`): the
pass-through bit and the coins of `A` at `2m + 1`. -/
private noncomputable def oddCoins (A : NUPPT) (m : ℕ) {post : List Bool → List Bool}
    (hpost : PolyTimeComputable post) :
    Bool × A.Coins (m + m + 1) ≃ (NUPPT.wrap (A.reparam oddParam) owpPredPre_poly hpost
      (fun _ => []) (.const 0) (fun _ => by simp) (.const 1)).Coins m :=
  ((Equiv.funUnique (Fin 1) Bool).symm.prodCongr (NUPPT.reparamCoins A oddParam m)).trans
    (Fin.appendEquiv 1 ((A.reparam oddParam).coinLen m))

/-- The encoding of the coins `(e, c)` is `[e] ++ c`. -/
private theorem ofFn_oddCoins (A : NUPPT) (m : ℕ) {post : List Bool → List Bool}
    (hpost : PolyTimeComputable post) (e : Bool) (c : A.Coins (m + m + 1)) :
    List.ofFn (oddCoins A m hpost (e, c)) =
      List.ofFn (fun _ : Fin 1 => e) ++ List.ofFn (NUPPT.reparamCoins A oddParam m c) := by
  simp only [oddCoins, Equiv.trans_apply]
  exact (ofFn_appendEquiv ((Equiv.funUnique (Fin 1) Bool).symm e) _).trans
    (congrArg (· ++ _) (by simp [List.ofFn_succ]))

/-- The odd-length inverter on `(e, c)` returns the first `|y|` bits of `A(1^{2m+1}, y ++ [e]; c)`. -/
private theorem glHalfOddInv_runAt (A : NUPPT) (m : ℕ) (y : List Bool) (e : Bool)
    (c : A.Coins (m + m + 1)) :
    (glHalfOddInv A).runAt m y (oddCoins A m glHalfInvPost_poly (e, c)) =
      (A.runAt (m + m + 1) (y ++ [e]) c).take y.length := by
  unfold glHalfOddInv
  rw [NUPPT.runAt_wrap (A.reparam oddParam) owpPredPre_poly glHalfInvPost_poly (fun _ => [])
    (.const 0) (fun _ => by simp) (.const 1) m y rfl (fun _ => e)
    (NUPPT.reparamCoins A oddParam m c) (oddCoins A m glHalfInvPost_poly (e, c))
    (ofFn_oddCoins A m glHalfInvPost_poly e c)]
  simp only [glHalfInvPost, owpPredPre, pairSndD_pairEncode, pairFstD_pairEncode,
    NUPPT.inArg_layout, NUPPT.inAdvice_layout, NUPPT.runAt_reparam]
  rfl

/-- The odd-length predictor on `(e, c)` returns the verdict of `A(1^{2m+1}, y ++ [e]; c)`. -/
private theorem glHalfOddPred_runAt (A : NUPPT) (m : ℕ) (y : List Bool) (e : Bool)
    (c : A.Coins (m + m + 1)) :
    (glHalfOddPred A).runAt m y (oddCoins A m polyTimeComputable_pairSndD (e, c)) =
      A.runAt (m + m + 1) (y ++ [e]) c := by
  unfold glHalfOddPred
  rw [NUPPT.runAt_wrap (A.reparam oddParam) owpPredPre_poly polyTimeComputable_pairSndD
    (fun _ => []) (.const 0) (fun _ => by simp) (.const 1) m y rfl (fun _ => e)
    (NUPPT.reparamCoins A oddParam m c) (oddCoins A m polyTimeComputable_pairSndD (e, c))
    (ofFn_oddCoins A m polyTimeComputable_pairSndD e c)]
  simp only [owpPredPre, pairSndD_pairEncode, NUPPT.inArg_layout, NUPPT.inAdvice_layout,
    NUPPT.runAt_reparam]
  rfl

/-- **Inversion at even length**: inverting `glHalf` at `2m` with `A` is inverting `glPad` at
`m` with the parameter-change machine `A.reparam (var + var)`. -/
theorem glHalf_invProbAt_even (P : PermFamily) (A : NUPPT) (m : ℕ) :
    P.glHalf.toFunFamily.invProbAt A (m + m) =
      P.toFunFamily.glPad.invProbAt (A.reparam (.add .var .var)) m := by
  rw [FunFamily.invProbAt_eq_uprob, FunFamily.invProbAt_eq_uprob]
  refine (OneWay.uprob_congr fun z => ?_).trans (uprob_comp_equiv
    ((Equiv.refl (Fin (m + m) → Bool)).prodCongr (NUPPT.reparamCoins A (.add .var .var) m)) _)
  obtain ⟨x, c⟩ := z
  simp only [Equiv.prodCongr_apply, Prod.map_apply, Equiv.coe_refl, id, NUPPT.runAt_reparam,
    PermFamily.toFunFamily_f, PermFamily.glHalf_f_even]
  exact Iff.rfl

/-- **Inversion at odd length**: inverting `glHalf` at `2m + 1` with `A` is at most inverting
`glPad` at `m` with the odd-length inverter. -/
theorem glHalf_invProbAt_odd_le (P : PermFamily) (A : NUPPT) (m : ℕ) :
    P.glHalf.toFunFamily.invProbAt A (m + m + 1) ≤
      P.toFunFamily.glPad.invProbAt (glHalfOddInv A) m := by
  rw [FunFamily.invProbAt_eq_uprob, FunFamily.invProbAt_eq_uprob]
  refine le_of_eq_of_le (uprob_comp_equiv (snocCoins m (A.Coins (m + m + 1))) _).symm ?_
  refine le_of_le_of_eq ?_ (uprob_comp_equiv
    ((Equiv.refl (Fin (m + m) → Bool)).prodCongr (oddCoins A m glHalfInvPost_poly)) _)
  refine uprob_mono fun w hw => ?_
  obtain ⟨z, e, c⟩ := w
  obtain ⟨x', hx', hfx'⟩ := hw
  simp only [snocCoins, Equiv.coe_fn_mk, Equiv.prodCongr_apply, Prod.map_apply, Equiv.coe_refl,
    id, PermFamily.toFunFamily_f, PermFamily.glHalf_f_odd] at hx' hfx' ⊢
  rw [← Fin.snoc_init_self x', PermFamily.glHalf_f_odd] at hfx'
  have hinit := congrArg Fin.init hfx'
  simp only [Fin.init_snoc] at hinit
  refine ⟨Fin.init x', ?_, hinit⟩
  rw [glHalfOddInv_runAt, ← ofFn_snoc_eq, hx', List.length_ofFn, ofFn_eq_init_append,
    List.take_left' List.length_ofFn]

/-- **Prediction at even length**: predicting `glHalfBit` from `glHalf` at `2m` with `A` is
predicting `⟨x, r⟩` from `glPad` at `m` with `A.reparam (var + var)`. -/
theorem glHalf_predProb_even (P : PermFamily) (A : NUPPT) (m : ℕ) :
    predProb (P.glHalf.f (m + m)) (glHalfBit (m + m)) (A.predictor (m + m) (m + m)) =
      predProb (P.toFunFamily.glPad.f m) (P.toFunFamily.glBit m)
        ((A.reparam (.add .var .var)).predictor m (m + m)) := by
  rw [predProb_glHalf_even]
  refine (predProb_coins_equiv _ _ _ _ (NUPPT.reparamCoins A (.add .var .var) m) fun y c => ?_).symm
  simp only [NUPPT.predictor, NUPPT.distinguisher, NUPPT.runAt_reparam]
  rfl

/-- **Prediction at odd length**: predicting `glHalfBit` from `glHalf` at `2m + 1` with `A` is
predicting `⟨x, r⟩` from `glPad` at `m` with the odd-length predictor. -/
theorem glHalf_predProb_odd (P : PermFamily) (A : NUPPT) (m : ℕ) :
    predProb (P.glHalf.f (m + m + 1)) (glHalfBit (m + m + 1)) (A.predictor (m + m + 1) (m + m + 1)) =
      predProb (P.toFunFamily.glPad.f m) (P.toFunFamily.glBit m)
        ((glHalfOddPred A).predictor m (m + m)) := by
  rw [predProb_glHalf_odd]
  refine (predProb_coins_equiv _ _ _ _ (oddCoins A m polyTimeComputable_pairSndD) fun y c => ?_).symm
  obtain ⟨e, c⟩ := c
  simp only [NUPPT.predictor, NUPPT.distinguisher]
  rw [glHalfOddPred_runAt, ← ofFn_snoc_eq]

/-- The absolute value of a negligible function is negligible. -/
private theorem negligible_abs {μ : ℕ → ℝ} (hμ : Negligible μ) : Negligible fun n => |μ n| :=
  hμ.mono ⟨0, fun n _ => by rw [abs_abs]⟩

/-! ## One-way permutations have a hard-core bit [PS10, Theorem 87.3, "(OWP)"] -/

/-- **One-way permutations have a hard-core bit** ([PS10, Theorem 87.3], the "(OWP)" clause,
and the stated purpose of [PS10, §3.4], p. 86: "the existence of OWPs implies the existence of
OWPs with a hard-core bit"): if `f` is a one-way permutation then the balanced Goldreich–Levin
permutation `g = glHalf f`, `g_n(x ‖ w) = f_{⌊n/2⌋}(x) ‖ w`, is a one-way permutation and
`glHalfBit`, `(x ‖ w) ↦ ⟨x, w|_{⌊n/2⌋}⟩`, is a hard-core predicate for it. This is the form of
Theorem 87.3 consumed by `owp_hardcore_prg` (Theorem 79.4), `cor_81_7`, `owp_commitment`
(Theorem 126.4) and the Chapter 4 headlines; `goldreich_levin` (the `FunFamily` form at even
lengths) cannot feed them (run-3 audit P4-1).

**Deviation:** the text's `g` lives on `{0,1}^{2n}`; odd lengths carry one pass-through bit
(see the module docstring). The text says hard-core "for `f`" (source error 26).

**Proof sketch.** Write `m := ⌊n/2⌋`, so that `n = m + m` or `n = m + m + 1`, and let
`𝓖 := P.toFunFamily.glPad` with `hG := hP.glPad : 𝓖.StrongOneWay` and
`hB := hP.glPad_hardCore : HardCore 𝓖 P.toFunFamily.glBit` (`goldreich_levin hP`).
*Easy (one-wayness clause):* from `hP.easy = ⟨F, hF, hFx⟩` the evaluator on `⟨1^n, z⟩`
computes `1^m` from `1^n` (unary halving: `polyTimeComputable_iterate` with state
`⟨1^k, 1^j⟩ ↦ ⟨1^{k−2}, 1^{j+1}⟩` for `R := var` rounds, reading the second component, or a
`Build/`-style primitive), cuts `z` after `m` bits (`polyTimeComputable_pairTakePoly`/
`pairDropPoly` on `⟨1^m, z⟩`) and outputs `F ⟨1^m, z.take m⟩ ++ z.drop m`
(`PolyTimeComputable.pairEncode`, `.comp`, `.append`); the identity with
`List.ofFn (P.glHalf.f n z)` is `PermFamily.glHalf_f_apply` (`List.ofFn` of the two blocks).
*One-wayness, even `n = m + m`:* for an inverter `A : NUPPT` of `glHalf`,
`NUPPT.exists_reparam A (mul (const 2) var)` gives `A'` with `A'.runAtL m y r = A.runAtL (2m) y r`
and coins `A.coins.subst (2·var)`, so `A'.Coins m ≃ A.Coins (m + m)` (`PolyExpr.eval_subst`,
`finCongr`); by `invProbAt_eq_uprob`, `uprob_comp_equiv` and `invProb_glHalf_even`,
`P.glHalf.toFunFamily.invProbAt A (m + m) = 𝓖.invProbAt A' m`, which is `≤ ν₁ m` with
`ν₁ := fun m => 𝓖.invProbAt A' m` negligible by `hG.hard A'`.
*One-wayness, odd `n = m + m + 1`:* `NUPPT.exists_split (const 1)` then `exists_reparam`
(`2·var + 1`) and `exists_comp` (post-processing `stripLast`) give `A''` at parameter `m` that
reads one coin `e`, calls `A` at `2m + 1` on `y ++ [e]` and drops the last bit of the answer;
`invProb_glHalf_odd_le` (with `invProbOpt_le_invProb`, a wrong-length answer of `A` failing on
both sides) bounds `P.glHalf.toFunFamily.invProbAt A (m + m + 1) ≤ 𝓖.invProbAt A'' m =: ν₂ m`,
negligible by `hG.hard A''`. *Combination:* `invProbAt A n ≤ ν₁ (n/2) + ν₂ (n/2)` for every
`n` (both terms nonnegative, `invProbAt_nonneg`), negligible by `Negligible.comp_div_two`,
`Negligible.add` and `Negligible.mono`.
*Hard-core, easy clause:* `⟨x, r⟩` on `⟨1^n, z⟩`: halve `1^n` as above, cut `z` into
`x := z.take m` and `r := (z.drop m).take m` (`pairTakePoly`/`pairDropPoly` on `⟨1^m, ·⟩`),
bitwise AND (`polyTimeComputable_pairXor`-style) and parity (a `polyTimeComputable_majority`-style
count modulo 2 by `polyTimeComputable_iterate`); the identity with `[glHalfBit n z]` unfolds
`glHalfBit` and `HardcoreBit.ip`.
*Hard-core, hardness:* for a predictor `A : NUPPT`, even `n = m + m`: `predProb_glHalf_even`
and the reparametrised `A'` (as above, with `NUPPT.predictor` in place of `inverter`) identify
`predProb (P.glHalf.f n) (glHalfBit n) (A.predictor n n)` with
`predProb (𝓖.f m) (P.toFunFamily.glBit m) (A'.predictor m (m + m))`, bounded by
`1/2 + ε₁ m` with `ε₁` negligible by `hB.hard A'`; odd `n = m + m + 1`: `predProb_glHalf_odd`
identifies it with the `glPad` experiment at `m` against `A''` built by
`NUPPT.exists_split (const 1)` (the pass-through bit is the first coin, passed as data and
appended to the input) and `exists_reparam`, bounded by `1/2 + ε₂ m` by `hB.hard A''`
(`uprob_comp_equiv` on the coin split `A''.Coins m ≃ Bool × A.Coins (m + m + 1)`). The single
negligible function of Definition 78.3 is `ε n := ε₁ (n/2) + ε₂ (n/2)` (`Negligible.comp_div_two`,
`Negligible.add`). -/
theorem OneWayPermutation.glHalf {P : PermFamily} (hP : OneWayPermutation P) :
    OneWayPermutation P.glHalf ∧ HardCore P.glHalf.toFunFamily glHalfBit := by
  have hG : P.toFunFamily.glPad.StrongOneWay := hP.glPad
  have hB : HardCore P.toFunFamily.glPad P.toFunFamily.glBit := hP.glPad_hardCore
  obtain ⟨F, hF, hFx⟩ := hP.easy
  refine ⟨⟨P.glHalf_easy hF hFx, fun A => ?_⟩, ⟨glHalfBit_easy, fun A => ?_⟩⟩
  · have h₁ := hG.hard (A.reparam (.add .var .var))
    have h₂ := hG.hard (glHalfOddInv A)
    refine (h₁.comp_div_two.add h₂.comp_div_two).mono ⟨0, fun n _ => ?_⟩
    have hn₁ := FunFamily.invProbAt_nonneg P.toFunFamily.glPad (A.reparam (.add .var .var)) (n / 2)
    have hn₂ := FunFamily.invProbAt_nonneg P.toFunFamily.glPad (glHalfOddInv A) (n / 2)
    rw [abs_of_nonneg (FunFamily.invProbAt_nonneg _ _ _), abs_of_nonneg (add_nonneg hn₁ hn₂)]
    obtain ⟨m, hm | hm⟩ : ∃ m, n = m + m ∨ n = m + m + 1 := ⟨n / 2, by omega⟩
    · subst hm
      rw [show (m + m) / 2 = m by omega] at hn₁ hn₂ ⊢
      rw [glHalf_invProbAt_even]
      linarith
    · subst hm
      rw [show (m + m + 1) / 2 = m by omega] at hn₁ hn₂ ⊢
      linarith [glHalf_invProbAt_odd_le P A m]
  · obtain ⟨ε₁, hε₁, hb₁⟩ := hB.hard (A.reparam (.add .var .var))
    obtain ⟨ε₂, hε₂, hb₂⟩ := hB.hard (glHalfOddPred A)
    refine ⟨fun n => |ε₁ (n / 2)| + |ε₂ (n / 2)|,
      (negligible_abs hε₁).comp_div_two.add (negligible_abs hε₂).comp_div_two, fun n => ?_⟩
    obtain ⟨m, hm | hm⟩ : ∃ m, n = m + m ∨ n = m + m + 1 := ⟨n / 2, by omega⟩
    · subst hm
      dsimp only
      rw [show (m + m) / 2 = m by omega]
      have key : predProb (P.glHalf.f (m + m)) (glHalfBit (m + m)) (A.predictor (m + m) (m + m)) ≤
          1 / 2 + ε₁ m := by
        rw [glHalf_predProb_even]; exact hb₁ m
      exact key.trans (by linarith [le_abs_self (ε₁ m), abs_nonneg (ε₂ m)])
    · subst hm
      dsimp only
      rw [show (m + m + 1) / 2 = m by omega]
      have key : predProb (P.glHalf.f (m + m + 1)) (glHalfBit (m + m + 1))
          (A.predictor (m + m + 1) (m + m + 1)) ≤ 1 / 2 + ε₂ m := by
        rw [glHalf_predProb_odd]; exact hb₂ m
      exact key.trans (by linarith [le_abs_self (ε₂ m), abs_nonneg (ε₁ m)])

/-- **One-way permutations with a hard-core bit exist if one-way permutations do**
[PS10, §3.4, p. 86]: the hypothesis `∃ P h, OneWayPermutation P ∧ HardCore P.toFunFamily h`
of `exists_commitment_of_owp_hardCore` (Theorem 126.4), `zk_proof_of_owp_levinReduction` and
`zk_proof_of_mem_NP_of_owp` (Theorem 124.1) follows from `∃ P, OneWayPermutation P` alone, by
`OneWayPermutation.glHalf`. -/
theorem exists_owp_hardCore (h : ∃ P : PermFamily, OneWayPermutation P) :
    ∃ (P : PermFamily) (b : ∀ n, (Fin n → Bool) → Bool),
      OneWayPermutation P ∧ HardCore P.toFunFamily b :=
  let ⟨P, hP⟩ := h
  ⟨P.glHalf, glHalfBit, hP.glHalf⟩

/-- **Pseudorandom generators from any one-way permutation** [PS10, §3.4, p. 84: "a PRG can
be constructed from any one-way permutation"; Theorems 79.4 and 87.3]: if a one-way
permutation exists then a secure pseudorandom generator exists, namely
`owpGenPRG P.glHalf glHalfBit`, `s ↦ glHalf f (s) ‖ glHalfBit s` (`owp_hardcore_prg` applied to
`OneWayPermutation.glHalf`). -/
theorem exists_securePRG_of_owp (h : ∃ P : PermFamily, OneWayPermutation P) :
    ∃ G : PRG, G.Secure :=
  let ⟨P, hP⟩ := h
  ⟨owpGenPRG P.glHalf glHalfBit, owp_hardcore_prg P.glHalf glHalfBit hP.glHalf.1 hP.glHalf.2⟩

end TCSlib.Cryptography
