import Mathlib.InformationTheory.Hamming
import Mathlib.Data.Nat.Choose.Bounds
import Mathlib.Data.Nat.Choose.Sum

set_option maxHeartbeats 0

set_option relaxedAutoImplicit false

set_option autoImplicit false

namespace CommunicationComplexity
variable {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ}
def ballVol (n t q : ℕ) : ℕ :=
  ∑ i ∈ Finset.range (t + 1), Nat.choose n i * (q - 1) ^ i
end CommunicationComplexity

namespace CommunicationComplexity
variable {α : Type*} [Fintype α] [DecidableEq α] {n : ℕ}
lemma ballVol_binary (n t : ℕ) :
    ballVol n t 2 = ∑ i ∈ Finset.range (t + 1), Nat.choose n i := by
  simp [ballVol]
end CommunicationComplexity
