import TCSlib.Complexity.BranchingPrograms.Barrington
import TCSlib.Complexity.BranchingPrograms.Eval

/-! Probe P6 (host `evalWith`).  Kernel `decide` only.
* C8 (`evalWith_single`) on a NON-permutation program of width 3 (a constant map and a
  non-injective map): one-hot in, one-hot at the yield out, for every input and start state.
* The push form really sums: from the all-ones vector the constant map collects mass 3.
* C6 (pull form) on a permutation instruction `Instr.ofPerm 0 sigma1 sigma2`, stated literally
  with `Equiv.ofBijective`, for every input and coordinate and a vector with distinct entries. -/

open BranchingProgram Equiv

namespace P6

def sel : Bool → ℕ → ℕ → ℕ := fun b u v => if b then v else u

/-- Width 3, two inputs: instruction 1 sends everything to `2` on `x₀ = 0` and is `i ↦ i/2`-like
(`![0, 0, 1]`) on `x₀ = 1`; instruction 2 is `![1, 1, 0]` / identity on `x₁`. -/
def B : BranchingProgram 3 2 :=
  ⟨[⟨0, fun _ => 2, ![0, 0, 1]⟩, ⟨1, ![1, 1, 0], id⟩]⟩

example : ¬ B.IsPermutation := by
  rw [isPermutation_iff]; decide

theorem single_all : ∀ x : Fin 2 → Bool, ∀ s : Fin 3,
    B.evalWith sel x (Pi.single s 1) = Pi.single (B.yield x s) 1 := by
  decide +kernel

-- push form sums: all-ones vector through the constant map
example : (⟨[⟨0, fun _ => 2, id⟩]⟩ : BranchingProgram 3 1).evalWith sel (fun _ => false)
    (fun _ => 1) = ![0, 0, 3] := by
  decide

/-- C6 on `ι = Instr.ofPerm 0 sigma1 sigma2`. -/
def ι : Instr 5 1 := Instr.ofPerm 0 sigma1 sigma2

theorem hι : ι.IsPermutation := Instr.isPermutation_ofPerm 0 sigma1 sigma2

def V : Fin 5 → ℕ := fun i => 10 ^ (i : ℕ)

theorem pull_form : ∀ x : Fin 1 → Bool, ∀ i : Fin 5,
    ι.stepWith sel x V i =
      sel (x ι.var) (V ((Equiv.ofBijective _ (ι.isPermutation_iff.1 hι).1).symm i))
        (V ((Equiv.ofBijective _ (ι.isPermutation_iff.1 hι).2).symm i)) := by
  -- `Equiv.ofBijective ⇑σ _ = σ`; then decide
  have h0 : Equiv.ofBijective _ (ι.isPermutation_iff.1 hι).1 = sigma1 := Equiv.ext fun _ => rfl
  have h1 : Equiv.ofBijective _ (ι.isPermutation_iff.1 hι).2 = sigma2 := Equiv.ext fun _ => rfl
  rw [h0, h1]
  decide +kernel

end P6
