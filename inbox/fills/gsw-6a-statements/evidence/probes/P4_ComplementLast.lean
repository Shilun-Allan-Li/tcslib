import TCSlib.Complexity.BranchingPrograms.Barrington

/-! Probe P4 (Lemma 2, `complementLast`).  Kernel `decide` only.
On Bar89's example program (P1), which five-cycle recognizes `A = {x | x₀ = x₁ = 1}` with output
`ρ = c[0,2,1,4,3]`, `complementLast ρ` yields `ρ⁻¹ ∘ B(x)` (C3): the identity on `A` and `ρ⁻¹`
off `A`, so it recognizes the complement with output `ρ⁻¹` (C12); its length is unchanged; only
the last instruction changes; the empty program is unchanged. -/

open BranchingProgram Equiv

namespace P4

def barEx : BranchingProgram 5 2 :=
  ⟨[Instr.ofPerm 0 1 sigma1, Instr.ofPerm 1 1 sigma2, Instr.ofPerm 0 1 sigma1⁻¹,
    Instr.ofPerm 1 1 sigma2⁻¹]⟩

def ρ : Perm (Fin 5) := List.formPerm [0, 2, 1, 4, 3]

-- C3's formula on every input
theorem yield_cl : ∀ x : Fin 2 → Bool,
    (barEx.complementLast ρ).yield x = ρ.symm ∘ barEx.yield x := by
  decide +kernel

-- identity on A, ρ⁻¹ off A (Bar89: "B'(x) = e if x ∈ A and B'(x) = σ⁻¹ if x ∉ A")
theorem yield_cl_cases : ∀ x : Fin 2 → Bool,
    (barEx.complementLast ρ).yield x = if x 0 && x 1 then id else ⇑ρ⁻¹ := by
  decide +kernel

-- the output ρ⁻¹ is a five-cycle
example : IsFiveCycle ρ⁻¹ := by decide +kernel

-- length unchanged (C3)
example : (barEx.complementLast ρ).length = barEx.length := by decide

-- only the last instruction changes: the first three maps agree on every point
example : ∀ k : Fin 3, ∀ i : Fin 5,
    ((barEx.complementLast ρ).instrs.getD k (Instr.ofPerm 0 1 1)).map1 i =
      (barEx.instrs.getD k (Instr.ofPerm 0 1 1)).map1 i := by
  decide +kernel

-- the empty program is unchanged
example : (⟨[]⟩ : BranchingProgram 5 2).complementLast ρ = ⟨[]⟩ := rfl

end P4
