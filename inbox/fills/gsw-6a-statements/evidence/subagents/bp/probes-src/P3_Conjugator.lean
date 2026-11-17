import TCSlib.Complexity.BranchingPrograms.Barrington

/-! Probe P3 (Lemma 1's explicit conjugator).
* computability: `#eval` of `conjugator` (it compiles; no `noncomputable`);
* the 24 five-cycles of `S₅` are exactly `List.formPerm (0 :: p)` for `p` a permutation of
  `[1,2,3,4]` (kernel `decide`);
* C10 on all 24 × 24 pairs: `conjugator σ τ * σ * (conjugator σ τ)⁻¹ = τ` (kernel `decide`,
  in `P3b_ConjugatorAll.lean`, timed separately), and by `#eval` here. -/

open BranchingProgram Equiv

namespace P3

/-- The 24 five-cycles `c[0, p₁, p₂, p₃, p₄]`. -/
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

example : fiveCycles.length = 24 := by decide
example : fiveCycles.Nodup := by decide +kernel
example : ∀ σ ∈ fiveCycles, IsFiveCycle σ := by decide +kernel
example : ∀ σ : Perm (Fin 5), IsFiveCycle σ → σ ∈ fiveCycles := by decide +kernel

-- computable: values of a conjugator
#eval (List.finRange 5).map (conjugator sigma1 sigma2)
#eval (List.finRange 5).map (conjugator (sigma2⁻¹ * sigma1⁻¹ * sigma2 * sigma1) sigma1)
-- the C10 identity on all 576 pairs, by evaluation
#eval fiveCycles.all fun σ => fiveCycles.all fun τ =>
  decide (conjugator σ τ * σ * (conjugator σ τ)⁻¹ = τ)
-- the conjugator is a bijection (never the degenerate branch) on all 576 pairs
#eval fiveCycles.all fun σ => fiveCycles.all fun τ =>
  decide (Function.Bijective (conjugatorFun σ τ))
-- outside five-cycles it may degenerate to `1` (C10 is stated under `IsFiveCycle` hypotheses)
#eval decide (conjugator 1 sigma1 = 1)

end P3
