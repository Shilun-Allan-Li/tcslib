/-
Copyright (c) 2026 Yichuan Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yichuan Wang
-/
import Mathlib.Computability.Language
import TCSlib.Complexity.CircuitComplexity.LayeredCircuit

/-!
# P/poly over layered circuits

The class of languages decided by polynomial-size non-uniform Boolean circuit
families, built on `BoolCircuit.LayeredCircuit` (the model used by the Razborov–Smolensky
development) and shaped after Mathlib's `Language.IsRegular`: a complexity class
is a predicate on languages.

## Main definitions

* `BoolCircuit.LayeredCircuitFamily` — one single-output circuit per input length, all layers finite.
* `Language.InLayeredSIZE` — the layered model's rendering of [AB09, Def 6.2].
* `Language.InLayeredPPoly` — the layered model's rendering of [AB09, Def 6.5].

The book's classes, over DAG circuits, are `Language.InSIZE` / `Language.InPPoly`
(`PPoly.lean`); the two `P/poly`s coincide (`Language.inPPoly_iff_inLayeredPPoly`,
`LayeredDAG.lean`), while fixed `SIZE(T)` classes differ (below).
* `BoolCircuit.LayeredPPoly` — the same class as a `Set (Language Bool)`.

## Main results

* `Language.inLayeredPPoly_iff` — `P/poly` membership repackaged as one family that
  carries its own size bound.

## Alphabet

Languages are over `Bool`, matching `Turing.FinEncoding`'s binary encodings and
cslib's `MultiTapeTM k Bool State`, so that a future `P ⊆ P/poly` is statable
without transport.  Circuits stay on `Fin 2` internally (the Razborov–Smolensky
gate sets are `GateOp (Fin 2)`); `finTwoEquiv` converts at the boundary.

## Divergences from Arora–Barak §6.1

All preserve the polynomial union `P/poly`; **none is claimed to preserve a
fixed class `SIZE(T)`**, and in general none does: `Language.allOnes` lies in
this file's `InLayeredSIZE (fun _ => 1)` (`SizeClasses.lean`), while [AB09, Def 6.1]
counts the `n` input vertices, so no size-`1` circuit exists there for `n ≥ 2`.
`Language.InLayeredSIZE` is the finite, layered, unbounded-fan-in, non-input-counting
size class of *this* model; quantitative transfer to AB's `SIZE(T)` needs an
explicit simulation with a transformed budget. AB Def 6.1 fixes fan-in 2; we use unbounded `stdGateOps`,
which AB calls "essentially without loss of generality" (fan-in `f` costs `f - 1`
gates) and which is AB's own convention for `AC` (Def 6.25) — for *polynomial-size
existence* the fan-in choice is immaterial (budgets change by the `f - 1` factor);
exact size budgets do feel it, which is part of why fixed `SIZE(T)` is not
preserved (above).  `P/poly` imposes no depth restriction. AB's basis is `{∧, ∨, ¬}`;
ours adds `id` (needed for layer padding) and recovers `∨` by De Morgan. AB counts
input vertices in `|C|` and allows arbitrary DAGs; we count non-input nodes and
require layering, costing `+n` and a factor `≤ s` respectively. AB writes
`∃ c, ∀ n, |C n| ≤ n ^ c`; we write `∃ a k, ∀ n, size ≤ a * (n + 1) ^ k`, which
repairs a degeneracy in AB's literal form (`n ^ c` forces `|C 0| ≤ 0`; over the book's DAG
model the literal union is in fact empty, `Language.setOf_inSIZE_pow_eq_empty` in `PPoly.lean`).
Further graph conventions, collected: a singleton output type does not forbid
unused nodes on earlier layers; inputs may go unread; `Gate.inputs` need not be
injective, so repeated wires are allowed — all harmless for computational
power, with size/depth accounting model-specific.  `stdGateOps` contains
`andGateOp 0`, the empty product, i.e. a **constant-one** operation; there is
no primitive constant-false (`NOT` of the empty `AND` provides it).

## Trap

`LayeredCircuit.size` is `Nat.card`-based, so it returns `0` on an infinite type:
without `LayeredCircuitFamily.finite`, `IsPolySize` would hold vacuously and `P/poly`
would be every language.

## References

* [AB09] S. Arora, B. Barak, *Computational Complexity: A Modern Approach*,
  Cambridge University Press, 2009.
-/

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace BoolCircuit

open LayeredCircuit

/-- A non-uniform family of single-output Boolean circuits, one per input length. -/
structure LayeredCircuitFamily where
  /-- The circuit handling inputs of length `n`. -/
  circuit : (n : ℕ) → LayeredCircuit (Fin 2) (Fin n) Unit
  /-- Every layer of every circuit in the family is finite. -/
  finite : ∀ n, (circuit n).Finite

namespace LayeredCircuitFamily

variable (C : LayeredCircuitFamily)

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

end LayeredCircuitFamily

end BoolCircuit

/-- `L ∈ SIZE(T)`: some `stdGateOps` family decides `L` with the length-`n`
circuit of size at most `T n`.  [AB09, Def 6.2] -/
def Language.InLayeredSIZE (T : ℕ → ℕ) (L : Language Bool) : Prop :=
  ∃ C : BoolCircuit.LayeredCircuitFamily,
    C.OnlyUsesGates BoolCircuit.stdGateOps ∧ (∀ n, (C.circuit n).size ≤ T n) ∧ C.language = L

/-- A language is in `P/poly` when some polynomial-size circuit family decides
it.  [AB09, Def 6.5] -/
def Language.InLayeredPPoly (L : Language Bool) : Prop :=
  ∃ a k : ℕ, L.InLayeredSIZE (fun n => a * (n + 1) ^ k)

/-- `P/poly` membership as one family carrying its own size bound. -/
theorem Language.inLayeredPPoly_iff (L : Language Bool) :
    L.InLayeredPPoly ↔ ∃ C : BoolCircuit.LayeredCircuitFamily,
      C.OnlyUsesGates BoolCircuit.stdGateOps ∧ C.IsPolySize ∧ C.language = L := by
  constructor
  · rintro ⟨a, k, C, hG, hS, hL⟩
    exact ⟨C, hG, ⟨a, k, hS⟩, hL⟩
  · rintro ⟨C, hG, ⟨a, k, hS⟩, hL⟩
    exact ⟨a, k, C, hG, hS, hL⟩

namespace BoolCircuit

/-- `P/poly` packaged as a set of languages, for `L ∈ LayeredPPoly` notation. -/
def LayeredPPoly : Set (Language Bool) :=
  {L | L.InLayeredPPoly}

/-- Set membership in `LayeredPPoly` agrees with the predicate `Language.InLayeredPPoly`. -/
@[simp]
theorem mem_LayeredPPoly_iff (L : Language Bool) : L ∈ LayeredPPoly ↔ L.InLayeredPPoly :=
  Iff.rfl

end BoolCircuit
