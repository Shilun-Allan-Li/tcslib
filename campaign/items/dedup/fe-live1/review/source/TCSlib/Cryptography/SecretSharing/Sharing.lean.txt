/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.SecretSharing.Shamir

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The algebra of Shamir sharings

For protocols built on Shamir's scheme it is the *relation* "the share vector `f` is a degree-`d`
sharing of the value `x`" that one reasons about, not the dealer's coins. This file introduces
that relation, `Shamir.IsSharing`, and proves that it is closed under the operations protocols
perform locally: adding share vectors adds the secrets, scaling scales, and multiplying share
vectors multiplies the secrets *at the cost of doubling the degree*. It also isolates
reconstruction as a fixed linear functional `Shamir.recombine`, whose coefficients depend on the
reconstructing set alone and not on the shares.

These two facts — local operations act on secrets, reconstruction is linear — are exactly what
the BGW protocol runs on; see `TCSlib.Cryptography.MPC.BGW`.

## Main definitions

* `TCSlib.Shamir.IsSharing d x f`: `f` is the evaluation vector of a polynomial of degree `≤ d`
  with constant term `x`.
* `TCSlib.Shamir.recombine A f`: the Lagrange recombination of the shares held by `A`, a fixed
  linear combination `∑ i ∈ A, recombineCoeff A i * f i`.

## Main results

* `IsSharing.add`, `IsSharing.smul`, `IsSharing.mul`, `IsSharing.sum`: closure properties.
* `IsSharing.recombine_eq`: any `d + 1` parties recombine to the shared value.
* `recombine_add`, `recombine_smul`, `recombine_sum`: recombination is linear in the shares.

## References

* [Sha79] A. Shamir, *How to share a secret*, Communications of the ACM 22(11), 1979.
* [BGW88] M. Ben-Or, S. Goldwasser, A. Wigderson, *Completeness theorems for non-cryptographic
  fault-tolerant distributed computation*, STOC 1988, §3.
* [AL17] G. Asharov, Y. Lindell, *A full proof of the BGW protocol for perfectly secure
  multiparty computation*, J. Cryptology 30(1), 2017, §3.
-/

namespace TCSlib.Shamir

open Finset Polynomial

variable {F : Type*} [Field F] {d e : ℕ} {x y : F} {f g : Party F → F}

/-- `IsSharing d x f` says the share vector `f` is a degree-`d` Shamir sharing of `x`: there is a
polynomial of degree `≤ d` with constant term `x` whose evaluation at each party's label is that
party's share. The dealer's output `Shamir.scheme.share` is the running example, but a sharing
may also arise from local computation on other sharings. [BGW88, §3] -/
def IsSharing (d : ℕ) (x : F) (f : Party F → F) : Prop :=
  ∃ p : F[X], p.degree < ((d + 1 : ℕ) : WithBot ℕ) ∧ p.eval 0 = x ∧ ∀ i, f i = p.eval (label i)

/-- What the dealer hands out is a degree-`(k-1)` sharing of the secret. -/
theorem isSharing_share [DecidableEq F] {k : ℕ} (hk : 0 < k) (sec : F)
    (q : degreeLT F (k - 1)) :
    IsSharing (k - 1) sec (fun i => (scheme k F).share sec q i) := by
  refine ⟨poly sec q, ?_, poly_eval_zero sec q, fun i => rfl⟩
  have : k - 1 + 1 = k := Nat.succ_pred_eq_of_pos hk
  rw [this]
  exact degree_poly_lt hk sec q

/-- A sharing of degree `d` is one of any larger degree. -/
theorem IsSharing.mono (h : IsSharing d x f) (hde : d ≤ e) : IsSharing e x f := by
  obtain ⟨p, hp, hp0, hpf⟩ := h
  exact ⟨p, lt_of_lt_of_le hp (by exact_mod_cast Nat.succ_le_succ hde), hp0, hpf⟩

/-- The constant share vector is a sharing of that constant: parties can introduce public
values into the computation without interaction. -/
theorem isSharing_const (d : ℕ) (c : F) : IsSharing d c (fun _ => c) :=
  ⟨C c, lt_of_le_of_lt degree_C_le (by exact_mod_cast Nat.succ_pos d), by simp, fun _ => by simp⟩

/-- **Addition gate.** Adding share vectors componentwise adds the shared values, with no
interaction and no growth in degree. [BGW88, §3] -/
theorem IsSharing.add (hf : IsSharing d x f) (hg : IsSharing d y g) :
    IsSharing d (x + y) (f + g) := by
  obtain ⟨p, hp, hp0, hpf⟩ := hf
  obtain ⟨r, hr, hr0, hrg⟩ := hg
  exact ⟨p + r, lt_of_le_of_lt (degree_add_le _ _) (max_lt hp hr), by simp [hp0, hr0],
    fun i => by simp [Pi.add_apply, hpf i, hrg i]⟩

/-- **Scalar multiplication gate.** Scaling every share by a public constant scales the shared
value. [BGW88, §3] -/
theorem IsSharing.smul (c : F) (hf : IsSharing d x f) : IsSharing d (c * x) (fun i => c * f i) := by
  obtain ⟨p, hp, hp0, hpf⟩ := hf
  refine ⟨C c * p, lt_of_le_of_lt (degree_mul_le _ _) ?_, by simp [hp0], fun i => by simp [hpf i]⟩
  exact lt_of_le_of_lt (add_le_add_right degree_C_le _) (by simpa using hp)

/-- **Multiplication gate, before degree reduction.** Multiplying share vectors componentwise
multiplies the shared values, but the degree adds: `d + e` instead of `d`. Undoing this growth is
the only step of BGW that requires interaction. [BGW88, §3] -/
theorem IsSharing.mul (hf : IsSharing d x f) (hg : IsSharing e y g) :
    IsSharing (d + e) (x * y) (f * g) := by
  obtain ⟨p, hp, hp0, hpf⟩ := hf
  obtain ⟨r, hr, hr0, hrg⟩ := hg
  refine ⟨p * r, lt_of_le_of_lt (degree_mul_le _ _) ?_, by simp [hp0, hr0],
    fun i => by simp [Pi.mul_apply, hpf i, hrg i]⟩
  calc p.degree + r.degree
      ≤ ((d : WithBot ℕ)) + (e : WithBot ℕ) := by
        exact add_le_add (Order.le_of_lt_succ (by exact_mod_cast hp))
          (Order.le_of_lt_succ (by exact_mod_cast hr))
    _ < ((d + e + 1 : ℕ) : WithBot ℕ) := by push_cast; exact_mod_cast Nat.lt_succ_self (d + e)

/-- A finite sum of degree-`d` sharings is a degree-`d` sharing of the sum. -/
theorem IsSharing.sum {ι : Type*} (s : Finset ι) {v : ι → F} {h : ι → Party F → F}
    (hs : ∀ i ∈ s, IsSharing d (v i) (h i)) :
    IsSharing d (∑ i ∈ s, v i) (fun j => ∑ i ∈ s, h i j) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using isSharing_const d (0 : F)
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    have hrest := ih (fun i hi => hs i (Finset.mem_insert_of_mem hi))
    have key : (fun j => ∑ i ∈ insert a s, h i j) = h a + (fun j => ∑ i ∈ s, h i j) := by
      funext j; simp [Finset.sum_insert ha]
    rw [key]
    exact (hs a (Finset.mem_insert_self a s)).add hrest

section Recombine

variable [DecidableEq F]

/-- The Lagrange recombination coefficient of party `i` inside the reconstructing set `A`: the
value at `0` of `i`'s Lagrange basis polynomial for `A`. It depends only on `A` — not on the
shares, and not on what is being shared. -/
noncomputable def recombineCoeff (A : Finset (Party F)) (i : Party F) : F :=
  (Lagrange.basis A label i).eval 0

/-- Reconstruction as a fixed linear functional of the shares: `∑ i ∈ A, λ_i · f i`. This is the
same value as `Shamir.scheme.reconstruct A f`, but written so that its linearity in `f` is
manifest; BGW's degree reduction is exactly an application of that linearity. [BGW88, §3] -/
noncomputable def recombine (A : Finset (Party F)) (f : Party F → F) : F :=
  ∑ i ∈ A, recombineCoeff A i * f i

theorem recombine_eq_eval_interpolate (A : Finset (Party F)) (f : Party F → F) :
    recombine A f = (Lagrange.interpolate A label f).eval 0 := by
  simp [recombine, recombineCoeff, Lagrange.interpolate_apply, eval_finset_sum, mul_comm]

theorem recombine_eq_reconstruct (A : Finset (Party F)) (f : Party F → F) {k : ℕ} :
    recombine A f = (scheme k F).reconstruct A f :=
  recombine_eq_eval_interpolate A f

/-- **Reconstruction.** Any `d + 1` parties recombine a degree-`d` sharing to the shared value.

**Proof sketch.** The sharing polynomial has degree `≤ d < #A` and agrees with the shares on the
`#A` distinct nodes of `A`, so it *is* the Lagrange interpolant of those shares; recombination
evaluates that interpolant at `0`, returning its constant term. -/
theorem IsSharing.recombine_eq (h : IsSharing d x f) {A : Finset (Party F)} (hA : d + 1 ≤ #A) :
    recombine A f = x := by
  obtain ⟨p, hp, hp0, hpf⟩ := h
  have hinj : Set.InjOn label (A : Set (Party F)) := label_injective.injOn
  have hdeg : p.degree < (#A : WithBot ℕ) := lt_of_lt_of_le hp (by exact_mod_cast hA)
  have : p = Lagrange.interpolate A label f :=
    Lagrange.eq_interpolate_of_eval_eq _ hinj hdeg (fun i _ => (hpf i).symm)
  rw [recombine_eq_eval_interpolate, ← this, hp0]

@[simp]
theorem recombine_add (A : Finset (Party F)) (f g : Party F → F) :
    recombine A (f + g) = recombine A f + recombine A g := by
  simp [recombine, mul_add, Finset.sum_add_distrib]

@[simp]
theorem recombine_smul (A : Finset (Party F)) (c : F) (f : Party F → F) :
    recombine A (fun i => c * f i) = c * recombine A f := by
  simp only [recombine, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- Recombination commutes with finite sums of share vectors. -/
theorem recombine_sum {ι : Type*} (A : Finset (Party F)) (s : Finset ι)
    (h : ι → Party F → F) :
    recombine A (fun j => ∑ i ∈ s, h i j) = ∑ i ∈ s, recombine A (h i) := by
  simp only [recombine, Finset.mul_sum]
  exact Finset.sum_comm

end Recombine

end TCSlib.Shamir
