/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.SetTheory.Cardinal.Finite

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Counting low-degree polynomials through prescribed points

Mathlib's `Lagrange.funEquivDegreeLT` says that a polynomial of degree `< #s` is the same data as
its values on a set `s` of `#s` distinct nodes. This file draws the consequence that secret
sharing (and, more generally, any "polynomial as a random object" argument) actually uses: if you
fix the values at only *some* of the nodes, the remaining polynomials are in bijection with the
free coordinates, so there are exactly `|F| ^ (#s - #t)` of them — a count that does not depend
on *which* values were prescribed.

Everything here is about polynomials only; no secret sharing notions appear. Shamir's scheme is
the special case `t = {0} ∪ (adversary's nodes)`.

## Main definitions

* `TCSlib.Interpolation.fixedEvalEquiv`: polynomials of degree `< #s` with prescribed values on
  `t ⊆ s` are in bijection with functions `↥(s \ t) → F`.

## Main results

* `TCSlib.Interpolation.exists_unique_degreeLT_eval_eq`: unique interpolation through `#s` nodes.
* `TCSlib.Interpolation.natCard_degreeLT_eval_eq`: there are exactly `|F| ^ (#s - #t)` such
  polynomials, independently of the prescribed values.
* `TCSlib.Interpolation.surjective_eval_of_subset`: any prescription on `t ⊆ s` is realizable.

## References

* [Sha79] A. Shamir, *How to share a secret*, Communications of the ACM 22(11), 1979.
* [Mathlib] `Mathlib/LinearAlgebra/Lagrange.lean`.
-/

namespace TCSlib.Interpolation

open Finset Polynomial

variable {F ι : Type*} [Field F] [DecidableEq ι] {v : ι → F} {s t : Finset ι}

/-- Through any prescription of values at `#s` distinct nodes there passes exactly one
polynomial of degree `< #s`, namely the Lagrange interpolant. [Mathlib, `Lagrange`] -/
theorem exists_unique_degreeLT_eval_eq (hvs : Set.InjOn v s) (w : ι → F) :
    ∃! p : F[X], p.degree < #s ∧ ∀ i ∈ s, p.eval (v i) = w i := by
  refine ⟨Lagrange.interpolate s v w, ⟨Lagrange.degree_interpolate_lt _ hvs,
    fun i hi => Lagrange.eval_interpolate_at_node _ hvs hi⟩, fun q hq => ?_⟩
  exact Lagrange.eq_interpolate_of_eval_eq _ hvs hq.1 hq.2

/-- Prescribing the values of a polynomial on a subset `t` of the nodes leaves exactly the
freedom of choosing its values on the remaining nodes: the polynomials of degree `< #s` taking
the values `w` on `t` correspond bijectively to functions `↥(s \ t) → F`.

**Proof sketch.** Transport the constraint along `Lagrange.funEquivDegreeLT`, which identifies
degree-`< #s` polynomials with their value vectors on `s`; the constraint becomes "this
coordinate vector is `w` on `t`", and such vectors are exactly arbitrary vectors on `s \ t`. -/
noncomputable def fixedEvalEquiv (hvs : Set.InjOn v s) (hts : t ⊆ s) (w : ι → F) :
    {p : degreeLT F #s // ∀ i ∈ t, eval (v i) p.1 = w i} ≃ (↥(s \ t) → F) where
  toFun p j := (Lagrange.funEquivDegreeLT hvs p.1) ⟨j.1, (mem_sdiff.1 j.2).1⟩
  invFun g :=
    ⟨(Lagrange.funEquivDegreeLT hvs).symm
      (fun i => if hi : i.1 ∈ t then w i.1 else g ⟨i.1, mem_sdiff.2 ⟨i.2, hi⟩⟩), by
        intro i hi
        have h := (Lagrange.funEquivDegreeLT hvs).apply_symm_apply
          (fun i : ↥s => if hi : i.1 ∈ t then w i.1 else g ⟨i.1, mem_sdiff.2 ⟨i.2, hi⟩⟩)
        have := congrFun h ⟨i, hts hi⟩
        simpa [Lagrange.funEquivDegreeLT, hi] using this⟩
  left_inv := by
    rintro ⟨p, hp⟩
    apply Subtype.ext
    apply (Lagrange.funEquivDegreeLT hvs).injective
    rw [(Lagrange.funEquivDegreeLT hvs).apply_symm_apply]
    funext i
    by_cases hi : i.1 ∈ t
    · simpa [hi, Lagrange.funEquivDegreeLT] using (hp i.1 hi).symm
    · simp [hi]
  right_inv := by
    intro g
    funext j
    have hj := mem_sdiff.1 j.2
    dsimp only
    rw [(Lagrange.funEquivDegreeLT hvs).apply_symm_apply]
    simp [hj.2]

/-- Every prescription of values on a subset `t` of the nodes is realized by some polynomial of
degree `< #s`. -/
theorem surjective_eval_of_subset (hvs : Set.InjOn v s) (hts : t ⊆ s) (w : ι → F) :
    ∃ p : F[X], p.degree < #s ∧ ∀ i ∈ t, p.eval (v i) = w i := by
  obtain ⟨p, hp⟩ := (fixedEvalEquiv hvs hts w).symm (fun _ => 0)
  exact ⟨p.1, mem_degreeLT.1 p.2, hp⟩

/-- **The count.** Over a finite field with `q` elements there are exactly `q ^ (#s - #t)`
polynomials of degree `< #s` taking prescribed values on `t ⊆ s`. The count is the same for
every prescription `w`; this uniformity is the whole content of perfect privacy for Shamir's
scheme. -/
theorem natCard_degreeLT_eval_eq (hvs : Set.InjOn v s) (hts : t ⊆ s) (w : ι → F) :
    Nat.card {p : degreeLT F #s // ∀ i ∈ t, eval (v i) p.1 = w i} = Nat.card F ^ (#s - #t) := by
  rw [Nat.card_congr (fixedEvalEquiv hvs hts w), Nat.card_fun, Nat.card_eq_finsetCard,
    Finset.card_sdiff, Finset.inter_eq_left.2 hts]

end TCSlib.Interpolation
