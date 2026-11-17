import TCSlib.Complexity.BranchingPrograms.Barrington

/-! Probe P1 (yield order).  Kernel `decide` only (`decide +kernel` for the 256-input
check: same kernel evaluation, skipping the elaborator's pre-evaluation, which hits
`maxRecDepth`).
(a) Bar89's example p004-b001, translated to BV14's order (map0 first) and 0-based variables,
    yields `List.formPerm [0,2,1,4,3]` (Bar89's (13254)) exactly when `x₀ = x₁ = 1`, else `id`.
(b) Bar89's width-2 XOR example p001-b002, `⟨7,(12),e⟩⟨4,e,(12)⟩⟨8,(12),e⟩`, translated to BV14's
    order and 0-based variables (x₇ ↦ 6, x₄ ↦ 3, x₈ ↦ 7), yields the transposition exactly when
    `x₇ ⊕ ¬x₄ ⊕ x₈`, else `id` (all 256 inputs).
(c) `yield_append`'s direction on a two-program example: `(B₁ ++ B₂).yield x = B₂.yield x ∘ B₁.yield x`,
    and NOT `B₁.yield x ∘ B₂.yield x`. -/

open BranchingProgram Equiv

namespace P1

/-- Bar89 p004-b001: ⟨1,(12345),e⟩⟨2,(13542),e⟩⟨1,(54321),e⟩⟨2,(24531),e⟩ (Bar89 order: the
`x_j = 1` map first), in BV14 order with variables 0, 1. -/
def barEx : BranchingProgram 5 2 :=
  ⟨[Instr.ofPerm 0 1 (List.formPerm [0, 1, 2, 3, 4]),
    Instr.ofPerm 1 1 (List.formPerm [0, 2, 4, 3, 1]),
    Instr.ofPerm 0 1 (List.formPerm [4, 3, 2, 1, 0]),
    Instr.ofPerm 1 1 (List.formPerm [1, 3, 4, 2, 0])]⟩

-- (54321) and (24531) are the inverses of (12345) and (13542):
example : (List.formPerm [4, 3, 2, 1, 0] : Perm (Fin 5)) = sigma1⁻¹ := by decide
example : (List.formPerm [1, 3, 4, 2, 0] : Perm (Fin 5)) = sigma2⁻¹ := by decide

theorem barEx_yield : ∀ x : Fin 2 → Bool,
    barEx.yield x = if x 0 && x 1 then ⇑(List.formPerm [0, 2, 1, 4, 3] : Perm (Fin 5)) else id := by
  decide

-- the accepted yield is the program-order commutator sigma2⁻¹ * sigma1⁻¹ * sigma2 * sigma1
theorem barEx_yield_comm : barEx.yield (fun _ => true) = ⇑(sigma2⁻¹ * sigma1⁻¹ * sigma2 * sigma1) := by
  decide

/-- The transposition of `Fin 2`. -/
def t : Perm (Fin 2) := Equiv.swap 0 1

/-- Bar89 p001-b002: ⟨7,(12),e⟩⟨4,e,(12)⟩⟨8,(12),e⟩ in BV14 order, variables x₇ ↦ 6, x₄ ↦ 3,
x₈ ↦ 7 (eight inputs). -/
def xorEx : BranchingProgram 2 8 :=
  ⟨[Instr.ofPerm 6 1 t, Instr.ofPerm 3 t 1, Instr.ofPerm 7 1 t]⟩

theorem xorEx_yield : ∀ x : Fin 8 → Bool,
    xorEx.yield x = if xor (xor (x 6) (!x 3)) (x 7) then ⇑t else id := by
  decide +kernel

/-- Two constant programs (one instruction each, both branches the same permutation). -/
def B₁ : BranchingProgram 5 1 := ⟨[Instr.ofPerm 0 sigma1 sigma1]⟩
def B₂ : BranchingProgram 5 1 := ⟨[Instr.ofPerm 0 sigma2 sigma2]⟩

theorem append_dir : ∀ x : Fin 1 → Bool, (B₁ ++ B₂).yield x = B₂.yield x ∘ B₁.yield x := by
  decide

theorem append_dir_perm : ∀ x : Fin 1 → Bool, (B₁ ++ B₂).yield x = ⇑(sigma2 * sigma1) := by
  decide

theorem append_not_other_dir : ∀ x : Fin 1 → Bool, (B₁ ++ B₂).yield x ≠ B₁.yield x ∘ B₂.yield x := by
  decide

end P1
