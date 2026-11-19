import TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.PolyRatio

/-! Probe U18-P1 (gsw-6b-u18-u19, C12; evidence only, no `native_decide`): the constant
`8·4^33·2 = 2^70` by `norm_num` and by kernel `decide`, and G16's two sides evaluated by `#eval`
at three small constant families (noise law: one seed, error 0). -/

open TCSlib.Cryptography TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW

example : 8 * 4 ^ 33 * 2 = 2 ^ 70 := by norm_num
example : 8 * 4 ^ 33 * 2 = 2 ^ 70 := by decide

/-- A constant toy family: dimension `n`, `m` samples, modulus `q`, residue width `ℓ`. -/
def toyFamily (n m q ℓ : ℕ) (hq : 2 ≤ q) (hℓ : q ≤ 2 ^ ℓ) : LWE.Family where
  parameters := fun _ => ⟨n, m, q, hq⟩
  noise := fun _ => ⟨Unit, fun _ => 0⟩
  dimensionBound := .const n
  samplesBound := .const m
  residueBits := .const ℓ
  dimension_le := fun _ => le_rfl
  samples_le := fun _ => le_rfl
  modulus_le_pow := fun _ => hℓ

/-- G16's two sides at `κ = 0` and noise bound `B`: `(lhs, rhs, lhs ≤ rhs)`. -/
def g16Sides (F : LWE.Family) (B : ℕ) : ℕ × ℕ × Bool :=
  let P := Parameters.ofFamily F 0
  let lhs := 8 * (P.width * bootNoise P (P.lwe.samples * B))
  let rhs := (pBoot F).eval 0 * B
  (lhs, rhs, decide (lhs ≤ rhs))

#eval g16Sides (toyFamily 1 8 4 2 (by norm_num) (by norm_num)) 1
#eval g16Sides (toyFamily 2 20 16 4 (by norm_num) (by norm_num)) 3
#eval g16Sides (toyFamily 3 40 257 9 (by norm_num) (by norm_num)) 2
