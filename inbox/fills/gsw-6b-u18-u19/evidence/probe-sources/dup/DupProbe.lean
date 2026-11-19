import TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.Asymptotic

/-! Duplication probes (gsw-6b-u18-u19): `exact?` on the statements of the helpers and of the
inline facts of the fills, at the head. Evidence only. -/

open TCSlib.Cryptography TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW Complexity

-- P1: the public helper, stated for an arbitrary `P` with the two reader equations.
example (F : LWE.Family) (κ : ℕ) (P : Parameters) (h1 : P.lwe = F.parameters κ)
    (h2 : P.width = F.residueBits.eval κ) :
    P.columns ≤ (F.dimensionBound.eval κ + 1) * F.residueBits.eval κ := by
  exact?

-- P2: `⌈log₂ N⌉ ≤ N`.
example (n : ℕ) : Nat.clog 2 n ≤ n := by
  exact?

-- P3: the input noise is at most the bootstrapped noise.
example (P : Parameters) (β : ℕ) : β ≤ bootNoise P β := by
  exact?

-- P4: the decryption-condition glue, for a general `P`.
example (P : Parameters) (y b p : ℕ) (hy : y ≤ b) (h : 8 * (P.width * b) ≤ p)
    (hp : p < P.lwe.modulus) : 2 * (P.width * y) < P.lwe.modulus / 2 := by
  exact?

-- P5: nonnegativity of a DLWE advantage.
example (P : LWE.Parameters) (χ : LWE.Noise) {ρ : Type} [Fintype ρ] [Nonempty ρ]
    (D : (Matrix (Fin P.samples) (Fin P.dimension) (ZMod P.modulus) ×
      (Fin P.samples → ZMod P.modulus)) → ρ → Bool) : 0 ≤ LWE.decisionAdvantage P χ D := by
  exact?

-- P6: nonnegativity of `distAdv`.
example {σ τ γ ρ : Type} [Fintype σ] [Fintype τ] [Fintype ρ] (X : σ → γ) (Y : τ → γ)
    (D : γ → ρ → Bool) : 0 ≤ distAdv X Y D := by
  exact?

-- P7: a polynomial times a negligible function plus a negligible function.
example (p : PolyExpr) {μ ν : ℕ → ℝ} (hμ : Negligible μ) (hν : Negligible ν) :
    Negligible fun n => (p.eval n : ℝ) * μ n + ν n := by
  exact?

-- P8: a double sum of a constant over `Fin a × Fin b`.
example (a b : ℕ) (c : ℝ) : ∑ _e : Fin a, ∑ _j : Fin b, c = a * (b * c) := by
  exact?
