import TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.Circular
import TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.LeveledSecurity

/-! gsw-6b-u15-u17, C11: `exact?` probes on the statements of the private helpers (those stated with public
terms only; `levelPosHybrid` is private, so the helpers about it are probed through the facts they combine)
and of G15's inner step, to find a published lemma stating them (evidence only). -/

open TCSlib.Cryptography TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW
open Encryption.PublicKey

set_option maxHeartbeats 4000000

-- P1: G15's inner step (the evaluation-key coins dropped)
example (P : Parameters) (χ : LWE.Noise) {ρ : Type*} [Fintype ρ] [Nonempty ρ] (μ : Bool)
    (D : PublicKey P × Ciphertext P → ρ → Bool) :
    acceptProb (fun r : Seeds P χ => ((fheView P χ μ r).1, (fheView P χ μ r).2.2)) D =
      acceptProb (realView P χ μ) D := by
  exact?

-- P2: `leveledView_eq_levelHybrid`
example (P : Parameters) (χ : LWE.Noise) (L : ℕ) (μ : Bool) :
    leveledView P χ L μ = levelHybrid P χ L μ L := by
  exact?

-- P3: `acceptProb_levelHybrid_zero_realView`
example (P : Parameters) (χ : LWE.Noise) (L : ℕ) (μ : Bool) {ρ : Type*} [Fintype ρ] [Nonempty ρ]
    (D : LeveledView P L → ρ → Bool) :
    acceptProb (levelHybrid P χ L μ 0) D = acceptProb (realView P χ μ) (challengeDist P χ L D) := by
  exact?

-- P4: `abs_acceptProb_id_levelReduction_sub_le`
example (P : Parameters) (χ : LWE.Noise) (L : ℕ) (μ : Bool) (e : Fin L) (j : Fin P.columns)
    {ρ : Type*} [Fintype ρ] [Nonempty ρ] (D : LeveledView P L → ρ → Bool) :
    |acceptProb (id : PublicKey P → PublicKey P) (levelReduction P χ L μ e j true D) -
        acceptProb (id : PublicKey P → PublicKey P) (levelReduction P χ L μ e j false D)| ≤
      2 * (P.columns * Regev.extractionError P.lwe) := by
  exact?

-- P5: the real-key identity at the end of the chain, `b = true`, `j` arbitrary, against `H_{e+1}` itself
-- (true only for `j = 0`; a published lemma for the general case would have to name the position hybrid)
example (P : Parameters) (χ : LWE.Noise) (L : ℕ) (μ : Bool) (e : Fin L)
    {ρ : Type*} [Fintype ρ] [Nonempty ρ] (D : LeveledView P L → ρ → Bool) :
    acceptProb (LWE.sample P.lwe χ) (levelReduction P χ L μ e ⟨0, Nat.pos_of_ne_zero (NeZero.ne _)⟩ true D) =
      acceptProb (levelHybrid P χ L μ (e.val + 1)) D := by
  exact?

-- P6: the averaging step (expected: `abs_uexp_sub_le`, used)
example {α : Type*} [Fintype α] (f g : α → ℝ) (c : ℝ) (hc : 0 ≤ c) (h : ∀ a, |f a - g a| ≤ c) :
    |uexp f - uexp g| ≤ c := by
  exact?
