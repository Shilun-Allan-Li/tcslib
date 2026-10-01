/-
Copyright (c) 2026 Yichuan Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yichuan Wang
-/
import Mathlib.Computability.Language
import TCSlib.BooleanAnalysis.RazborovSmolensky.ACpGates

/-!
# P/poly

The class of languages decided by polynomial-size non-uniform Boolean circuit
families, built on `ACP.FeedForward` (the model used by the Razborov–Smolensky
development) and shaped after Mathlib's `Language.IsRegular`: a complexity class
is a predicate on languages.

## Main definitions

* `ACP.CircuitFamily` — one single-output circuit per input length, all layers finite.
* `Language.InSIZE` — [AB09, Def 6.2].
* `Language.InPPoly` — [AB09, Def 6.5], `P/poly = ⋃_c SIZE(n^c)`.
* `ACP.PPoly` — the same class as a `Set (Language Bool)`.

## Main results

* `Language.inPPoly_iff` — `P/poly` membership repackaged as one family that
  carries its own size bound.

## Alphabet

Languages are over `Bool`, matching `Turing.FinEncoding`'s binary encodings and
cslib's `MultiTapeTM k Bool State`, so that a future `P ⊆ P/poly` is statable
without transport.  Circuits stay on `Fin 2` internally (the Razborov–Smolensky
gate sets are `GateOp (Fin 2)`); `finTwoEquiv` converts at the boundary.

## Divergences from Arora–Barak §6.1

All are class-preserving. AB Def 6.1 fixes fan-in 2; we use unbounded `AC_GateOps`,
which AB calls "essentially without loss of generality" (fan-in `f` costs `f - 1`
gates) and which is AB's own convention for `AC` (Def 6.25) — fan-in matters only
under a depth restriction, and `P/poly` imposes none. AB's basis is `{∧, ∨, ¬}`;
ours adds `id` (needed for layer padding) and recovers `∨` by De Morgan. AB counts
input vertices in `|C|` and allows arbitrary DAGs; we count non-input nodes and
require layering, costing `+n` and a factor `≤ s` respectively. AB writes
`∃ c, ∀ n, |C n| ≤ n ^ c`; we write `∃ a k, ∀ n, size ≤ a * (n + 1) ^ k`, which
repairs a degeneracy in AB's literal form (`n ^ c` forces `|C 0| ≤ 0`).

## Trap

`FeedForward.size` is `Nat.card`-based, so it returns `0` on an infinite type:
without `CircuitFamily.finite`, `IsPolySize` would hold vacuously and `P/poly`
would be every language.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.
-/

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace ACP

open FeedForward

/-- A non-uniform family of single-output Boolean circuits, one per input length. -/
structure CircuitFamily where
  /-- The circuit handling inputs of length `n`. -/
  circuit : (n : ℕ) → FeedForward (Fin 2) (Fin n) Unit
  /-- Every layer of every circuit in the family is finite. -/
  finite : ∀ n, (circuit n).Finite

namespace CircuitFamily

variable (C : CircuitFamily)

/-- The family accepts `w` when the circuit for length `w.length` outputs `1`.
Words are `List Bool`; `finTwoEquiv` converts at the circuit boundary. -/
def Accepts (w : List Bool) : Prop :=
  (C.circuit w.length).eval₁ (fun i => finTwoEquiv.symm (w.get i)) = 1

/-- The language decided by the family. -/
def language : Language Bool :=
  {w | C.Accepts w}

/-- Membership in the decided language, unfolded to the circuit's output. -/
@[simp]
theorem mem_language_iff (w : List Bool) :
    w ∈ C.language ↔
      (C.circuit w.length).eval₁ (fun i => finTwoEquiv.symm (w.get i)) = 1 :=
  Iff.rfl

/-- Every circuit in the family draws its gates from `S`. -/
def OnlyUsesGates (S : Set (GateOp (Fin 2))) : Prop :=
  ∀ n, (C.circuit n).onlyUsesGates S

/-- The family has polynomial size. -/
def IsPolySize : Prop :=
  ∃ a k : ℕ, ∀ n, (C.circuit n).size ≤ a * (n + 1) ^ k

end CircuitFamily

end ACP

/-- `L ∈ SIZE(T)`: some `AC_GateOps` family decides `L` with the length-`n`
circuit of size at most `T n`.  [AB09, Def 6.2] -/
def Language.InSIZE (T : ℕ → ℕ) (L : Language Bool) : Prop :=
  ∃ C : ACP.CircuitFamily,
    C.OnlyUsesGates ACP.AC_GateOps ∧ (∀ n, (C.circuit n).size ≤ T n) ∧ C.language = L

/-- A language is in `P/poly` when some polynomial-size circuit family decides
it.  [AB09, Def 6.5] -/
def Language.InPPoly (L : Language Bool) : Prop :=
  ∃ a k : ℕ, L.InSIZE (fun n => a * (n + 1) ^ k)

/-- `P/poly` membership as one family carrying its own size bound. -/
theorem Language.inPPoly_iff (L : Language Bool) :
    L.InPPoly ↔ ∃ C : ACP.CircuitFamily,
      C.OnlyUsesGates ACP.AC_GateOps ∧ C.IsPolySize ∧ C.language = L := by
  constructor
  · rintro ⟨a, k, C, hG, hS, hL⟩
    exact ⟨C, hG, ⟨a, k, hS⟩, hL⟩
  · rintro ⟨C, hG, ⟨a, k, hS⟩, hL⟩
    exact ⟨a, k, C, hG, hS, hL⟩

namespace ACP

/-- `P/poly` packaged as a set of languages, for `L ∈ PPoly` notation. -/
def PPoly : Set (Language Bool) :=
  {L | L.InPPoly}

/-- Set membership in `PPoly` agrees with the predicate `Language.InPPoly`. -/
@[simp]
theorem mem_PPoly_iff (L : Language Bool) : L ∈ PPoly ↔ L.InPPoly :=
  Iff.rfl

end ACP
