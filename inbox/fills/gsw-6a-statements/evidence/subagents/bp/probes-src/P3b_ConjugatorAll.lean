import TCSlib.Complexity.BranchingPrograms.Barrington

/-! Probe P3b: C10 on all 24 × 24 pairs of five-cycles by kernel `decide` (timed by the check
log's start/end stamps). -/

open BranchingProgram Equiv

namespace P3b

def fiveCycles : List (Perm (Fin 5)) :=
  -- the 24 lists 0 :: p, p a permutation of [1,2,3,4] (written out: `List.permutations` is
  -- not kernel-reducible)
  [List.formPerm [0, 1, 2, 3, 4],
    List.formPerm [0, 1, 2, 4, 3],
    List.formPerm [0, 1, 3, 2, 4],
    List.formPerm [0, 1, 3, 4, 2],
    List.formPerm [0, 1, 4, 2, 3],
    List.formPerm [0, 1, 4, 3, 2],
    List.formPerm [0, 2, 1, 3, 4],
    List.formPerm [0, 2, 1, 4, 3],
    List.formPerm [0, 2, 3, 1, 4],
    List.formPerm [0, 2, 3, 4, 1],
    List.formPerm [0, 2, 4, 1, 3],
    List.formPerm [0, 2, 4, 3, 1],
    List.formPerm [0, 3, 1, 2, 4],
    List.formPerm [0, 3, 1, 4, 2],
    List.formPerm [0, 3, 2, 1, 4],
    List.formPerm [0, 3, 2, 4, 1],
    List.formPerm [0, 3, 4, 1, 2],
    List.formPerm [0, 3, 4, 2, 1],
    List.formPerm [0, 4, 1, 2, 3],
    List.formPerm [0, 4, 1, 3, 2],
    List.formPerm [0, 4, 2, 1, 3],
    List.formPerm [0, 4, 2, 3, 1],
    List.formPerm [0, 4, 3, 1, 2],
    List.formPerm [0, 4, 3, 2, 1]]

theorem conjugator_conj_all : ∀ σ ∈ fiveCycles, ∀ τ ∈ fiveCycles,
    conjugator σ τ * σ * (conjugator σ τ)⁻¹ = τ := by
  decide +kernel

end P3b
