import Mathlib.Computability.TMComputable
import Mathlib.Data.Real.Basic
import Mathlib.Data.List.Defs
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Asymptotics.Asymptotics
import Mathlib.Computability.Language
import Mathlib.Analysis.SpecialFunctions.Log.Base


variable {α β γ : Type}
variable (l : Filter ℕ)

notation f " =O[" l "] " g => Asymptotics.IsBigO l f g

namespace Asymptotics

def IsOmega [Norm E] [Norm F] (l : Filter α) (f : α → E) (g : α → F) : Prop :=
  Asymptotics.IsBigO l g f

end Asymptotics


structure Algorithm (α : Type) (β : Type) where
  (func : α → β)
  (time : ℕ → ℝ)
  (length : ℕ → ℕ)


theorem composition_time (f : Algorithm α β) (g : Algorithm β γ) :
∃h : Algorithm α γ,
  h.func = g.func ∘ f.func ∧
  h.time = f.time + g.time ∘ f.length ∧
  h.length = g.length ∘ f.length
:= sorry


def self_composition (func : α → α) : ℕ → α → α
  | 0 => id
  | n+1 => func ∘ (self_composition func n)


theorem loop_time (f : Algorithm α α) (n : ℕ) :
  ∃h : Algorithm α α,
    h.func = self_composition f.func n ∧
    h.time = (fun (m : ℕ) => (Finset.sum (Finset.range n) (fun i => (f.time ∘ self_composition f.length i) m))) ∧
    h.length = fun (m : ℕ) => self_composition f.length n m
  := by
  use { func := self_composition f.func n,
        time := fun (m : ℕ) => (Finset.sum (Finset.range n) (fun i => (f.time ∘ self_composition f.length i) m)),
        length := fun (m : ℕ) => self_composition f.length n m }


noncomputable def add_alg : Algorithm (ℕ × ℕ) ℕ :=
  { func := fun (p : ℕ × ℕ) => p.1 + p.2,
    time := fun (n : ℕ) => Real.log n,
    length := fun (n : ℕ) => n }


-- Harvey-Hoeven algorithm
noncomputable def mult_alg : Algorithm (ℕ × ℕ) ℕ :=
  { func := fun (p : ℕ × ℕ) => p.1 * p.2,
    time := fun (n : ℕ) => Real.log n * Real.log (Real.log n),
    length := fun (n : ℕ) => 2*n }


noncomputable def matrix_mult_alg : Algorithm (ℕ × ℕ) ℕ :=
  { func := fun (p : ℕ × ℕ) => p.1 + p.2,
    time := fun (n : ℕ) => Real.log n,
    length := fun (n : ℕ) => n }


def polytime_computible (f : α → β) :=
  ∃(alg : Algorithm α β), alg.func = f ∧ ∃(c : ℕ), Asymptotics.IsBigO l alg.time (fun (n : ℕ) => (n^c : ℝ))


theorem mergesort :
  ∃(alg : Algorithm (List ℕ) (List ℕ)),
    ∀ (lst : List ℕ), ∀ i j : Fin (alg.func lst).length, i < j → (alg.func lst).get i < (alg.func lst).get j ∧
    ∃ inv_perm : List ℕ → List ℕ, inv_perm (alg.func lst) = lst ∧
    Asymptotics.IsBigO l alg.time (fun (n : ℕ) => (n * Real.log n : ℝ)) ∧
    alg.length = id
  := sorry


-- def P (A : Language α) : Prop := ∃(alg : Algorithm (List α) Bool),
-- ∀ (x : List α), x ∈ A ↔ alg.func x = true ∧
--   ∃(c : ℕ), Asymptotics.IsBigO l alg.time (fun (n : ℕ) => (n^c : ℝ))


def NP (A : Language α) : Prop := ∃(alg : Algorithm (List α) Bool),
  ∃(c : ℕ),
    Asymptotics.IsBigO l alg.time (fun (n : ℕ) => (n^c : ℝ)) ∧
    ∀ (x : List α), x ∈ A ↔ ∃ (w : List α), w.length < x.length^c ∧ alg.func (w ++ x) = true


theorem master_thm (alg : Algorithm α β) (recur_step : Algorithm α β) (a b : ℝ) : (∀ n, alg.time n = a * alg.time (n) + recur_step.time n) →
 let c_crit := Real.log a / Real.log b
 (∃ (c : ℝ), c < c_crit ∧ Asymptotics.IsBigO l recur_step.time (fun (m : ℕ) => (m^c : ℝ)) →  Asymptotics.IsTheta l alg.time (fun (m : ℕ) => (m^c_crit : ℝ))) ∧
 (∃ (k : ℝ), Asymptotics.IsTheta l recur_step.time (fun (m : ℕ) => (m^c_crit * (Real.log n)^k : ℝ)) →  Asymptotics.IsTheta l alg.time (fun (m : ℕ) => (m^c_crit * (Real.log n)^(k+1) : ℝ))) ∧
 (∃ (c : ℝ), c > c_crit ∧ Asymptotics.IsOmega l recur_step.time (fun (m : ℕ) => (m^c : ℝ)) →  Asymptotics.IsTheta l alg.time recur_step.time)
 := sorry


-- list decoding
-- parallel repetition! Holenstein's proof
