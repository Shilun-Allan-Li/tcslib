/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.LinearAlgebra.Lagrange
import TCSlib.Cryptography.SecretSharing.Defs
import TCSlib.Cryptography.SecretSharing.Interpolation

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Shamir's `k`-out-of-`n` secret sharing scheme

The dealer holding a secret `sec ∈ F` picks a uniformly random polynomial
`p = sec + a₁X + ⋯ + a_{k-1}X^{k-1}` and hands party `a` the share `p(a)`, where the parties are
labelled by *nonzero* field elements. Any `k` parties recover `sec = p(0)` by Lagrange
interpolation; any `k - 1` or fewer learn nothing at all.

The randomness is modelled as the polynomial `q` with `p = sec + X · q`, i.e. as an element of
`degreeLT F (k-1)`, so that "uniform coins" means "uniform `q`" and the privacy bijection is
literally translation by a fixed polynomial.

## Main definitions

* `TCSlib.Shamir.Party`: the parties, labelled by nonzero elements of `F`.
* `TCSlib.Shamir.poly`, `TCSlib.Shamir.scheme`: the dealer's polynomial and the scheme itself.

## Main results

* `TCSlib.Shamir.correct`: any `k` parties reconstruct the secret.
* `TCSlib.Shamir.perfectPrivacy`: any at most `k - 1` parties have a view independent of the
  secret; combined with `Scheme.PerfectPrivacy.card_view_eq`, every view has equally many coin
  preimages under every secret.

## References

* [Sha79] A. Shamir, *How to share a secret*, Communications of the ACM 22(11), 1979, §2–3.
* [Bei11] A. Beimel, *Secret-sharing schemes: a survey*, IWCC 2011, §2.1.
-/

namespace TCSlib.Shamir

open Finset Polynomial TCSlib.SecretSharing

variable {F : Type*} [Field F] {k : ℕ}

/-- The parties of Shamir's scheme, labelled by the nonzero elements of `F`; the label `0` is
reserved for the secret. -/
abbrev Party (F : Type*) [Field F] := {a : F // a ≠ 0}

/-- The labels of the parties, as evaluation nodes. -/
abbrev label : Party F → F := Subtype.val

theorem label_injective : Function.Injective (label (F := F)) := Subtype.val_injective

/-- The dealer's polynomial for secret `sec` and coins `q`: `sec + X · q`, of degree `< k`.
[Sha79, §2] -/
noncomputable def poly (sec : F) (q : degreeLT F (k - 1)) : F[X] := C sec + X * q.1

@[simp]
theorem poly_eval_zero (sec : F) (q : degreeLT F (k - 1)) : (poly sec q).eval 0 = sec := by
  simp [poly]

theorem poly_eval (sec : F) (q : degreeLT F (k - 1)) (a : F) :
    (poly sec q).eval a = sec + a * q.1.eval a := by simp [poly]

/-- The dealer's polynomial really has degree `< k`. -/
theorem degree_poly_lt (hk : 0 < k) (sec : F) (q : degreeLT F (k - 1)) :
    (poly sec q).degree < (k : WithBot ℕ) := by
  have hq : q.1.degree < ((k - 1 : ℕ) : WithBot ℕ) := mem_degreeLT.1 q.2
  have hXq : (X * q.1 : F[X]).degree < (k : WithBot ℕ) := by
    rcases eq_or_ne q.1 0 with h0 | h0
    · rw [h0, mul_zero, degree_zero]
      exact WithBot.bot_lt_coe _
    · have hlt : q.1.natDegree < k - 1 := by
        rw [degree_eq_natDegree h0] at hq; exact_mod_cast hq
      have h2 : 1 + q.1.natDegree < k := by omega
      rw [degree_mul, degree_X, degree_eq_natDegree h0]
      exact_mod_cast h2
  refine lt_of_le_of_lt (degree_add_le _ _) (max_lt ?_ hXq)
  exact lt_of_le_of_lt degree_C_le (by exact_mod_cast hk)

/-- Shamir's scheme: share `sec` as the evaluations of a random degree-`< k` polynomial with
constant term `sec`, and reconstruct by Lagrange interpolation at `0`. [Sha79, §2] -/
noncomputable def scheme (k : ℕ) (F : Type*) [Field F] [DecidableEq F] :
    Scheme (Party F) F F (degreeLT F (k - 1)) where
  share sec q a := (poly sec q).eval (label a)
  reconstruct A f := (Lagrange.interpolate A label f).eval 0

theorem scheme_share [DecidableEq F] (sec : F) (q : degreeLT F (k - 1)) (a : Party F) :
    (scheme k F).share sec q a = (poly sec q).eval (label a) := rfl

/-- Reconstruction only reads the shares of the reconstructing set. -/
theorem localReconstruct [DecidableEq F] : (scheme k F).LocalReconstruct := by
  intro A f g hfg
  simp only [scheme]
  congr 1
  exact Lagrange.interpolate_eq_of_values_eq_on _ _ hfg

/-- **Correctness.** Any `k` (or more) parties reconstruct the secret exactly, whatever the
dealer's coins were. [Sha79, §2]

**Proof sketch.** The dealer's polynomial `p` has degree `< k ≤ #A`, and it agrees with the
shares on the `#A` distinct nodes of `A`, so by uniqueness of Lagrange interpolation it *is*
the interpolant of those shares. Evaluating at `0` returns its constant term, the secret. -/
theorem correct [DecidableEq F] (hk : 0 < k) :
    (scheme k F).Correct (AccessStructure.threshold k) := by
  intro A hA sec q
  have hinj : Set.InjOn label (A : Set (Party F)) := label_injective.injOn
  have hdeg : (poly sec q).degree < (#A : WithBot ℕ) :=
    lt_of_lt_of_le (degree_poly_lt hk sec q) (by exact_mod_cast hA)
  have : Lagrange.interpolate A label ((scheme k F).share sec q) = poly sec q :=
    (Lagrange.eq_interpolate_of_eval_eq _ hinj hdeg (fun i _ => rfl)).symm
  change (Lagrange.interpolate A label ((scheme k F).share sec q)).eval 0 = sec
  rw [this, poly_eval_zero]

/-- **Perfect privacy.** For any set `B` of at most `k - 1` parties and any two secrets there is
a bijection of the dealer's coins carrying one secret's `B`-view to the other's; so the shares
held by `B` carry no information whatsoever about the secret. [Sha79, §3]

**Proof sketch.** Let `δ = sec - sec'`. Interpolate through the `#B ≤ k - 1` points
`(b, δ / b)` (legitimate: party labels are nonzero) to get `r` of degree `< #B ≤ k - 1`, and
translate the coins by `r`. Then for `b ∈ B`,
`sec' + b·(q + r)(b) = sec' + b·q(b) + δ = sec + b·q(b)`, which is exactly the share `b` would
have received from `sec`. Translation by a fixed element is a bijection, so no view is gained
or lost. -/
theorem perfectPrivacy [DecidableEq F] :
    (scheme k F).PerfectPrivacy (AccessStructure.threshold k) := by
  intro B hB sec sec'
  have hBcard : #B < k := by simpa using lt_of_not_ge (by simpa using hB)
  have hinj : Set.InjOn label (B : Set (Party F)) := label_injective.injOn
  set r : F[X] := Lagrange.interpolate B label (fun b => (sec - sec') / label b) with hr
  have hrdeg : r ∈ degreeLT F (k - 1) := by
    refine mem_degreeLT.2 (lt_of_lt_of_le (Lagrange.degree_interpolate_lt _ hinj) ?_)
    exact_mod_cast Nat.le_sub_one_of_lt hBcard
  refine ⟨Equiv.addRight (⟨r, hrdeg⟩ : degreeLT F (k - 1)), fun q b hb => ?_⟩
  have hb0 : (label b) ≠ 0 := b.2
  have hrb : r.eval (label b) = (sec - sec') / label b :=
    Lagrange.eval_interpolate_at_node _ hinj hb
  simp only [scheme_share, poly_eval, Equiv.coe_addRight]
  have : ((⟨r, hrdeg⟩ : degreeLT F (k - 1)) + q).1 = q.1 + r := by
    simp [add_comm]
  rw [show (q + (⟨r, hrdeg⟩ : degreeLT F (k - 1))).1 = q.1 + r from rfl]
  rw [eval_add, hrb]
  field_simp
  ring

/-- **Perfect privacy, counting form.** Over a finite field, for a set `B` of at most `k - 1`
parties and *any* candidate view `w`, the number of coin choices producing that view is
`|F| ^ (k - 1 - #B)` — the same number for every secret and every view. So the adversary's view
is uniform on all of `(B → F)` and carries no information.

**Proof sketch.** Writing the dealer's polynomial as `sec + X · q`, party `b` receiving the share
`w b` pins down `q(b) = (w b - sec) / b` (party labels are nonzero). So the coin choices
consistent with the view are the polynomials of degree `< k - 1` through `#B` prescribed points,
and `Interpolation.natCard_degreeLT_eval_eq` counts these as `|F| ^ (k - 1 - #B)`, a count not
depending on the prescribed values and hence not on `sec`. -/
theorem natCard_coins_view [DecidableEq F] [Fintype F] (hk : 0 < k) (hkF : k ≤ Fintype.card F)
    {B : Finset (Party F)} (hB : #B < k) (sec : F) (w : Party F → F) :
    Nat.card {q : degreeLT F (k - 1) // ∀ b ∈ B, (scheme k F).share sec q b = w b} =
      Nat.card F ^ (k - 1 - #B) := by
  -- Pick a set `s` of `k - 1` parties containing `B` to serve as interpolation nodes.
  have hcard : Fintype.card (Party F) = Fintype.card F - 1 := by
    simp
  have hBle : #B ≤ k - 1 := Nat.le_sub_one_of_lt hB
  obtain ⟨s, hBs, -, hs⟩ :=
    Finset.exists_subsuperset_card_eq (Finset.subset_univ B) hBle
      (by rw [Finset.card_univ, hcard]; omega)
  have hinj : Set.InjOn label (s : Set (Party F)) := label_injective.injOn
  -- Consistency with the view is exactly a prescription of `q`'s values on `B`.
  have hiff : ∀ q : degreeLT F (k - 1),
      (∀ b ∈ B, (scheme k F).share sec q b = w b) ↔
        (∀ b ∈ B, eval (label b) q.1 = (w b - sec) / label b) := by
    intro q
    refine forall_congr' fun b => forall_congr' fun hb => ?_
    have hb0 : label b ≠ 0 := b.2
    rw [scheme_share, poly_eval]
    constructor
    · intro h; rw [eq_div_iff hb0, ← h]; ring
    · intro h; rw [h]; field_simp; ring
  rw [Nat.card_congr (Equiv.subtypeEquivRight hiff)]
  have := Interpolation.natCard_degreeLT_eval_eq (v := label) (s := s) (t := B) hinj hBs
    (fun b => (w b - sec) / label b)
  rw [hs] at this
  rw [this]

end TCSlib.Shamir
