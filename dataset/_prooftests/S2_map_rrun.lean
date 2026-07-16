import Mathlib.Tactic.Common
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Nat.Log
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Data.Fintype.Inv
import Mathlib.Data.Nat.Bitwise
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Probability.ProbabilityMassFunction.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.Convex.Integral
import Mathlib.Probability.ConditionalProbability
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Prod
import Mathlib.Probability.UniformOn

namespace CommunicationComplexity
end CommunicationComplexity

set_option maxHeartbeats 0

set_option relaxedAutoImplicit false

set_option autoImplicit false

namespace CommunicationComplexity
inductive Deterministic.FiniteMessage.Protocol (X Y α : Type*) where
  | output (val : α) : Protocol X Y α
  | alice {β : Type} [Fintype β] [Nonempty β]
      (f : X → β) (P : β → Protocol X Y α) :
      Protocol X Y α
  | bob {β : Type} [Fintype β] [Nonempty β]
      (f : Y → β) (P : β → Protocol X Y α) :
      Protocol X Y α
end CommunicationComplexity

namespace CommunicationComplexity.Deterministic.FiniteMessage.Protocol
variable {X Y α : Type*}
def run (p : Protocol X Y α) (x : X) (y : Y) : α :=
  match p with
  | Deterministic.FiniteMessage.Protocol.output val => val
  | Deterministic.FiniteMessage.Protocol.alice f P => (P (f x)).run x y
  | Deterministic.FiniteMessage.Protocol.bob f P => (P (f y)).run x y
end CommunicationComplexity.Deterministic.FiniteMessage.Protocol

set_option maxHeartbeats 0

set_option relaxedAutoImplicit false

set_option autoImplicit false

namespace CommunicationComplexity.Deterministic.FiniteMessage.Protocol
variable {X Y X₁ Y₁ X₂ Y₂ α α₁ α₂ β : Type*}
def map (g : α → β) : Protocol X Y α → Protocol X Y β
  | .output a => .output (g a)
  | Protocol.alice f P =>
      Protocol.alice f (fun b => (P b).map g)
  | Protocol.bob f P =>
      Protocol.bob f (fun b => (P b).map g)
end CommunicationComplexity.Deterministic.FiniteMessage.Protocol

namespace CommunicationComplexity.Deterministic.FiniteMessage.Protocol
variable {X Y X₁ Y₁ X₂ Y₂ α α₁ α₂ β : Type*}
@[simp]
theorem map_run (g : α → β) (p : Protocol X Y α) (x : X) (y : Y) :
    (p.map g).run x y = g (p.run x y) := by
  induction p <;> simp [map, run, *]
end CommunicationComplexity.Deterministic.FiniteMessage.Protocol

set_option maxHeartbeats 0

set_option relaxedAutoImplicit false

set_option autoImplicit false

open CommunicationComplexity
open MeasureTheory

namespace CommunicationComplexity.PublicCoin
abbrev FiniteMessage.Protocol (Ω : Type*) (X Y α : Type*) :=
  Deterministic.FiniteMessage.Protocol (Ω × X) (Ω × Y) α
end CommunicationComplexity.PublicCoin

namespace CommunicationComplexity.PublicCoin.FiniteMessage.Protocol
variable {Ω : Type*} {X Y α : Type*}
def rrun (p : Protocol Ω X Y α) (x : X) (y : Y) (ω : Ω) : α :=
  p.run (ω, x) (ω, y)
end CommunicationComplexity.PublicCoin.FiniteMessage.Protocol

set_option maxHeartbeats 0

set_option relaxedAutoImplicit false

set_option autoImplicit false

namespace CommunicationComplexity.PublicCoin.FiniteMessage.Protocol
variable {Ω Ω' Ω₁ Ω₂ X Y α α₁ α₂ β : Type*}
abbrev map (g : α → β) (p : Protocol Ω X Y α) : Protocol Ω X Y β :=
  Deterministic.FiniteMessage.Protocol.map g p
end CommunicationComplexity.PublicCoin.FiniteMessage.Protocol

namespace CommunicationComplexity.PublicCoin.FiniteMessage.Protocol
variable {Ω Ω' Ω₁ Ω₂ X Y α α₁ α₂ β : Type*}
@[simp]
theorem map_rrun (g : α → β) (p : Protocol Ω X Y α)
    (x : X) (y : Y) (ω : Ω) :
    (p.map g).rrun x y ω = g (p.rrun x y ω) := by
  simp [map, rrun, Deterministic.FiniteMessage.Protocol.map_run]
end CommunicationComplexity.PublicCoin.FiniteMessage.Protocol
