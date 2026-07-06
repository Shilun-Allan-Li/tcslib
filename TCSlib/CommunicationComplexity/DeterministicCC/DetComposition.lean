/-
Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Lucy Horowitz, Timothe Kasriel, Mihir Singhal
-/

import TCSlib.CommunicationComplexity.DeterministicCC.FiniteMessage
import Mathlib.Algebra.BigOperators.Fin

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# Monadic Structure of Finite-Message Protocols

## Main results

- `Deterministic.FiniteMessage.Protocol.map`: Map a function over the output of a protocol
- `Deterministic.FiniteMessage.Protocol.bind`: Sequentially compose two protocols (monadic bind)
- `Deterministic.FiniteMessage.Protocol.prod`: Product of two protocols with disjoint input types
- `Deterministic.FiniteMessage.Protocol.pi`: k-fold product of protocols with heterogeneous types

## References

- Original formalization by Lucy Horowitz, Timothe Kasriel, Mihir Singhal
-/

namespace CommunicationComplexity

namespace Deterministic.FiniteMessage.Protocol

variable {X Y X₁ Y₁ X₂ Y₂ α α₁ α₂ β : Type*}

/-- Map a function over the output of a protocol. -/
def map (g : α → β) : Protocol X Y α → Protocol X Y β
  | .output a => .output (g a)
  | Protocol.alice f P =>
      Protocol.alice f (fun b => (P b).map g)
  | Protocol.bob f P =>
      Protocol.bob f (fun b => (P b).map g)

@[simp]
theorem map_run (g : α → β) (p : Protocol X Y α) (x : X) (y : Y) :
    (p.map g).run x y = g (p.run x y) := by
  induction p <;> simp [map, run, *]

@[simp]
theorem map_complexity (g : α → β) (p : Protocol X Y α) :
    (p.map g).complexity = p.complexity := by
  induction p <;> simp [map, complexity, *]

/-- Bind: replace each output `a` in `p` with `q a`. -/
def bind : Protocol X Y α → (α → Protocol X Y β) → Protocol X Y β
  | .output a, q => q a
  | Protocol.alice f P, q =>
      Protocol.alice f (fun b => (P b).bind q)
  | Protocol.bob f P, q =>
      Protocol.bob f (fun b => (P b).bind q)

@[simp]
theorem bind_run (p : Protocol X Y α) (q : α → Protocol X Y β)
    (x : X) (y : Y) :
    (p.bind q).run x y = (q (p.run x y)).run x y := by
  induction p <;> simp [bind, run, *]

private theorem finset_sup_add_const {ι : Type*} [Fintype ι] [Nonempty ι]
    (f : ι → ℕ) (c : ℕ) :
    Finset.univ.sup (fun i => f i + c) =
      Finset.univ.sup f + c := by
  apply le_antisymm
  · apply Finset.sup_le; intro i _
    exact Nat.add_le_add (Finset.le_sup (Finset.mem_univ i)) le_rfl
  · have ⟨j, _, hj⟩ := Finset.exists_mem_eq_sup Finset.univ Finset.univ_nonempty f
    rw [hj]
    exact Finset.le_sup (f := fun i => f i + c) (Finset.mem_univ j)

theorem bind_complexity_const (p : Protocol X Y α)
    (q : α → Protocol X Y β)
    (c : ℕ) (hc : ∀ a, (q a).complexity = c) :
    (p.bind q).complexity = p.complexity + c := by
  induction p with
  | output a => simp [bind, complexity, hc]
  | alice f P ih =>
    simp only [bind, complexity, ih]
    rw [finset_sup_add_const]; omega
  | bob f P ih =>
    simp only [bind, complexity, ih]
    rw [finset_sup_add_const]; omega

/-- Product of two protocols with disjoint input types. Runs `p1` on
the first components `(X₁, Y₁)` and `p2` on the second `(X₂, Y₂)`,
pairing the outputs. -/
def prod (p1 : Protocol X₁ Y₁ α₁) (p2 : Protocol X₂ Y₂ α₂) :
    Protocol (X₁ × X₂) (Y₁ × Y₂) (α₁ × α₂) :=
  match p1 with
  | .output a1 =>
      (p2.comap Prod.snd Prod.snd).map (fun a2 => (a1, a2))
  | Protocol.alice f P =>
      Protocol.alice (f ∘ Prod.fst)
        (fun b => (P b).prod p2)
  | Protocol.bob f P =>
      Protocol.bob (f ∘ Prod.fst)
        (fun b => (P b).prod p2)

@[simp]
theorem prod_run (p1 : Protocol X₁ Y₁ α₁) (p2 : Protocol X₂ Y₂ α₂)
    (x : X₁ × X₂) (y : Y₁ × Y₂) :
    (p1.prod p2).run x y =
      (p1.run x.1 y.1, p2.run x.2 y.2) := by
  induction p1 <;> simp [prod, run, *]

theorem prod_complexity (p1 : Protocol X₁ Y₁ α₁) (p2 : Protocol X₂ Y₂ α₂) :
    (p1.prod p2).complexity =
      p1.complexity + p2.complexity := by
  induction p1 with
  | output a1 => simp [prod, complexity]
  | alice f P ih =>
    simp only [prod, complexity, ih]
    rw [finset_sup_add_const]; omega
  | bob f P ih =>
    simp only [prod, complexity, ih]
    rw [finset_sup_add_const]; omega

variable {k : ℕ} {Xf Yf : Fin k → Type*} {αf : Fin k → Type*}

/-- Pi (k-fold product) of protocols with heterogeneous input/output
types. Runs each `p i` on the `i`-th components, collecting outputs. -/
def pi :
    {k : ℕ} → {Xf : Fin k → Type*} → {Yf : Fin k → Type*} →
    {αf : Fin k → Type*} →
    ((i : Fin k) → Protocol (Xf i) (Yf i) (αf i)) →
      Protocol ((i : Fin k) → Xf i) ((i : Fin k) → Yf i)
        ((i : Fin k) → αf i)
  | 0, _, _, _, _ => .output (fun i => i.elim0)
  | _ + 1, _, _, _, p =>
      let head := (p 0).comap (· 0 : ((i : Fin (_ + 1)) → _) → _)
                              (· 0 : ((i : Fin (_ + 1)) → _) → _)
      let tail := (pi (fun i => p i.succ)).comap
                    (fun (x : (i : Fin (_ + 1)) → _) (i : Fin _) => x i.succ)
                    (fun (y : (i : Fin (_ + 1)) → _) (i : Fin _) => y i.succ)
      head.bind (fun a => tail.map (fun as => Fin.cons a as))

@[simp]
theorem pi_run
    (p : (i : Fin k) → Protocol (Xf i) (Yf i) (αf i))
    (x : (i : Fin k) → Xf i) (y : (i : Fin k) → Yf i) :
    (pi p).run x y =
      fun i => (p i).run (x i) (y i) := by
  induction k with
  | zero =>
    simp only [pi, run]
    ext i; exact i.elim0
  | succ k ih =>
    simp only [pi, bind_run, comap_run, map_run, ih]
    ext i; refine Fin.cases ?_ ?_ i <;> simp [Fin.cons]

theorem pi_complexity
    (p : (i : Fin k) → Protocol (Xf i) (Yf i) (αf i)) :
    (pi p).complexity =
      ∑ i, (p i).complexity := by
  induction k with
  | zero =>
    simp only [pi, complexity, Finset.univ_eq_empty, Finset.sum_empty]
  | succ k ih =>
    simp only [pi]
    have htail : ∀ a,
        (((pi (fun i => p i.succ)).comap
          (fun (x : (i : Fin (_ + 1)) → _) (i : Fin _) => x i.succ)
          (fun (y : (i : Fin (_ + 1)) → _) (i : Fin _) => y i.succ)).map
          (fun as => Fin.cons a as)).complexity =
        ∑ i : Fin k, (p i.succ).complexity := by
      intro a; simp [ih]
    rw [bind_complexity_const _ _ _ htail, Fin.sum_univ_succ]; simp

end Deterministic.FiniteMessage.Protocol

end CommunicationComplexity
