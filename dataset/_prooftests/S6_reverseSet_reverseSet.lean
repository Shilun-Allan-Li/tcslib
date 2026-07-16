import Mathlib.Tactic.Common
import Mathlib.Data.Tree.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Nat.Log
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Data.Fintype.Inv
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Set.Card
import Mathlib.Order.Defs.PartialOrder
import Mathlib.Tactic.Ring
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.Set.SymmDiff
import Mathlib.Data.Fintype.Powerset
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
import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntegrableOn
import PFR.ForMathlib.Entropy.Basic
import Mathlib.MeasureTheory.VectorMeasure.Decomposition.Jordan
import Mathlib.Tactic
import Mathlib.InformationTheory.KullbackLeibler.Basic
import Mathlib.Probability.Moments.SubGaussian
import PFR.Kullback

namespace CommunicationComplexity
end CommunicationComplexity
namespace ProbabilityTheory
end ProbabilityTheory

set_option maxHeartbeats 0

set_option relaxedAutoImplicit false

set_option autoImplicit false

open CommunicationComplexity
open MeasureTheory ProbabilityTheory

open CommunicationComplexity
open scoped BigOperators

namespace CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound
variable (n : ℕ+)
def reverseSet (S : Set (Fin n)) : Set (Fin n) :=
  {i | Fin.rev i ∈ S}
end CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound

namespace CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound
variable (n : ℕ+)
theorem reverseSet_reverseSet (S : Set (Fin n)) :
    reverseSet n (reverseSet n S) = S := by
  ext i
  simp [reverseSet]
end CommunicationComplexity.Functions.Disjointness.RandomizedLowerBound
