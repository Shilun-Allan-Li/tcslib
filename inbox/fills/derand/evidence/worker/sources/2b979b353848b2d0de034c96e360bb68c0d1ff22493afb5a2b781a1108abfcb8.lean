import TCSlib.Cryptography.Randomness.Derandomization

set_option maxHeartbeats 0
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace DerandEvidence

open Complexity Turing

/-- A zero time coefficient cannot witness a total finite computation. -/
theorem positive_coefficient {M : FinTM Bool} {f : List Bool → List Bool}
    {C : ℕ} {T : ℕ → ℕ}
    (hM : M.ComputesFunInTime f (fun n => C * T n)) : 0 < C := by
  by_contra hC
  have hzero : C = 0 := by omega
  have h := (FinTM.computesFunInTime_iff _ _ _).mp hM []
  apply FinTM.not_computesInTime_zero M [] (f [])
  simpa only [hzero, Nat.zero_mul] using h

example (i : ℕ) : SeedMajority.word 0 i = [] := by
  rw [SeedMajority.word_eq]
  exact List.take_zero

open Classical in
example (V : Language Bool) (x : List Bool) :
    SeedMajority.count V x 0 1 = if pairEncode x [] ∈ V then 1 else 0 := by
  rw [SeedMajority.count_succ, SeedMajority.count_zero, Nat.zero_add,
    SeedMajority.word_eq, List.take_zero]

example {d : ℕ} (hd : 0 < d) :
    TCSlib.Cryptography.Randomness.Derand.ceilRoot d 0 = 0 :=
  TCSlib.Cryptography.Randomness.Derand.ceilRoot_zero d

example {m : ℕ} :
    Randomized.randProb m (fun r => r.take 0 = []) = 1 := by
  rw [Randomized.randProb_take (Nat.zero_le m) (fun r => r = [])]
  norm_num [Randomized.randProb_eq]

#print axioms positive_coefficient

end DerandEvidence
