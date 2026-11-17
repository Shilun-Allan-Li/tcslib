import TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.PolyRatio

/-! Probe P7 (gsw-6b statements, check 7): the constants settled at the statement phase.
All `#eval` (evidence, not proof; `Nat.clog` is well-founded recursion).
* **G8 `decDepth_le`**: `decDepth P ≤ 9⌈log₂ N⌉ + 2⌈log₂(ℓ + ⌈log₂ N⌉ + 3)⌉ + 21`, over
  `n ∈ [0, 8]`, `ℓ ∈ [1, 40]` and `q ∈ {2, 3, 2^(ℓ−1)+1, 2^ℓ − 1, 2^ℓ}` (those `≥ 2` and `≤ 2^ℓ`):
  violations, and the minimal slack.
* **No term linear in `ℓ`**: `decDepth` at `n = 1`, `q = 2^ℓ`, `ℓ = 2^j` for `j ≤ 12`, next to
  `9·log₂ ℓ`: it grows by about `9` per doubling of `ℓ`.
* **G13 `bootNoise_le`**: `bootNoise P β ≤ 4^33·N^19·(ℓ + ⌈log₂ N⌉ + 3)^4·(2β)` on the same grid,
  `β ∈ {0, 1, 5, 1000}`.
* **The derivation of G13**: (i) `2^⌈log₂ y⌉ < 2y` for `1 ≤ y ≤ 100000` (so `4^⌈log₂ y⌉ ≤ 4y²`);
  (ii) `4^(9a + 2b + 22) ≤ 4^33·N^18·X^4` on the grid, `a = ⌈log₂ N⌉`, `X = ℓ + a + 3`,
  `b = ⌈log₂ X⌉`; (iii) the constant `8·4^33·2 = 2^70` of `pBoot`.
* **G16 `bootRatio_le_poly`** with the explicit `pBoot`: `8·(ℓ·bootNoise P (m·B)) ≤ pBoot(κ)·B`
  at `P = ofFamily F κ` for two sample families, `κ ≤ 30`, `B ∈ {1, 3}`; and G17's hypothesis
  `pBoot(κ)·B < q(κ)` is satisfiable (family `F1`, `q = 2^(κ+2)`, `B = 1`: the first `κ` found).
-/

open TCSlib.Cryptography
open TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW
open Complexity

namespace P7

/-- GSW parameters `(n, m = 2, q, ℓ)` when `2 ≤ q ≤ 2^ℓ`. -/
def mk? (n q ℓ : ℕ) : Option Parameters :=
  if h : 2 ≤ q ∧ q ≤ 2 ^ ℓ then some ⟨⟨n, 2, q, h.1⟩, ℓ, h.2⟩ else none

def grid : List Parameters :=
  (List.range 9).flatMap fun n => (List.range 40).flatMap fun i =>
    let ℓ := i + 1
    ([2, 3, 2 ^ (ℓ - 1) + 1, 2 ^ ℓ - 1, 2 ^ ℓ].eraseDups).filterMap fun q => mk? n q ℓ

def rhs8 (P : Parameters) : ℕ :=
  9 * Nat.clog 2 P.columns + 2 * Nat.clog 2 (P.width + Nat.clog 2 P.columns + 3) + 21

/-- (checked, violations, minimal slack) of G8's closed form. -/
def g8 : ℕ × ℕ × ℕ :=
  grid.foldl (fun (c, v, sl) P =>
    (c + 1, v + (if decDepth P ≤ rhs8 P then 0 else 1), min sl (rhs8 P - decDepth P)))
    (0, 0, 1000)

def rhs13 (P : Parameters) (β : ℕ) : ℕ :=
  4 ^ 33 * P.columns ^ 19 * (P.width + Nat.clog 2 P.columns + 3) ^ 4 * (2 * β)

/-- (checked, violations) of G13. -/
def g13 : ℕ × ℕ :=
  grid.foldl (fun (c, v) P => [0, 1, 5, 1000].foldl (fun (c, v) β =>
    (c + 1, v + (if bootNoise P β ≤ rhs13 P β then 0 else 1))) (c, v)) (0, 0)

/-- (i): violations of `2^⌈log₂ y⌉ < 2y`, `1 ≤ y ≤ 100000`. -/
def stepI : ℕ := ((List.range 100000).filter fun i => ¬ 2 ^ Nat.clog 2 (i + 1) < 2 * (i + 1)).length

/-- (ii): violations of `4^(9a + 2b + 22) ≤ 4^33·N^18·X^4` on the grid. -/
def stepII : ℕ := (grid.filter fun P =>
  let a := Nat.clog 2 P.columns
  let X := P.width + a + 3
  ¬ 4 ^ (9 * a + 2 * Nat.clog 2 X + 22) ≤ 4 ^ 33 * P.columns ^ 18 * X ^ 4).length

/-- decDepth at `n = 1`, `q = 2^ℓ`, `ℓ = 2^j`, with `⌈log₂ ℓ⌉`. -/
def growth : List (ℕ × ℕ × ℕ) := (List.range 13).filterMap fun j =>
  (mk? 1 (2 ^ 2 ^ j) (2 ^ j)).map fun P => (P.width, decDepth P, 9 * Nat.clog 2 P.width)

/-- A sample noise law: seeds `Fin 3`, errors `−1, 0, 1`. -/
def χ1 : LWE.Noise := ⟨Fin 3, fun i => (i.val : ℤ) - 1⟩

/-- Sample family 1: `n = κ + 1`, `m = 4(κ+2)² + 2κ`, `q = 2^(κ+2)`, `ℓ = κ + 2`. -/
def F1 : LWE.Family where
  parameters κ := ⟨κ + 1, 4 * (κ + 2) ^ 2 + 2 * κ, 2 ^ (κ + 2),
    le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) (Nat.le_add_left 2 κ))⟩
  noise _ := χ1
  dimensionBound := .add .var (.const 1)
  samplesBound := .add (.mul (.const 4) (.pow (.add .var (.const 2)) 2)) (.mul (.const 2) .var)
  residueBits := .add .var (.const 2)
  dimension_le _ := le_rfl
  samples_le _ := le_rfl
  modulus_le_pow _ := le_rfl

/-- Sample family 2: `n = 2κ`, `m = 3κ + 5`, `q = 3^(κ+1)`, `ℓ = 2κ + 2` (`3 ≤ 4`), with loose
bounds `d = 2κ + 1`, `s = 3κ + 9`. -/
def F2 : LWE.Family where
  parameters κ := ⟨2 * κ, 3 * κ + 5, 3 ^ (κ + 1),
    le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) (Nat.le_add_left 1 κ))⟩
  noise _ := χ1
  dimensionBound := .add (.mul (.const 2) .var) (.const 1)
  samplesBound := .add (.mul (.const 3) .var) (.const 9)
  residueBits := .add (.mul (.const 2) .var) (.const 2)
  dimension_le κ := by show 2 * κ ≤ 2 * κ + 1; omega
  samples_le κ := by show 3 * κ + 5 ≤ 3 * κ + 9; omega
  modulus_le_pow κ := by
    show 3 ^ (κ + 1) ≤ 2 ^ (2 * κ + 2)
    rw [show 2 * κ + 2 = 2 * (κ + 1) by ring, pow_mul]
    exact Nat.pow_le_pow_left (by norm_num) _

/-- G16: (checked, violations, min ratio rhs/lhs as ℕ) over `κ ≤ 30`, `B ∈ {1, 3}`. -/
def g16 (F : LWE.Family) : ℕ × ℕ × ℕ :=
  (List.range 31).foldl (fun (c, v, r) κ => [1, 3].foldl (fun (c, v, r) B =>
    let P := Parameters.ofFamily F κ
    let lhs := 8 * (P.width * bootNoise P (P.lwe.samples * B))
    let rhs := (pBoot F).eval κ * B
    (c + 1, v + (if lhs ≤ rhs then 0 else 1), min r (rhs / max lhs 1))) (c, v, r)) (0, 0, 10 ^ 400)

end P7

open P7
#eval ("grid size", grid.length)
#eval ("G8 decDepth_le (checked, violations, min slack)", g8)
#eval ("G13 bootNoise_le (checked, violations)", g13)
#eval ("derivation (i) violations of 2^clog y < 2y, y ≤ 100000", stepI)
#eval ("derivation (ii) violations of 4^(9a+2b+22) ≤ 4^33 N^18 X^4", stepII)
#eval ("derivation (iii) 8 * 4^33 * 2 = 2^70", decide (8 * 4 ^ 33 * 2 = 2 ^ 70))
#eval ("growth (ℓ, decDepth, 9⌈log₂ ℓ⌉) at n = 1, q = 2^ℓ", growth)
#eval ("G16 F1 (checked, violations, min rhs/lhs)", g16 F1)
#eval ("G16 F2 (checked, violations, min rhs/lhs)", g16 F2)
#eval ("pBoot F1 at κ = 0..3", (List.range 4).map fun κ => (pBoot F1).eval κ)
#eval ("G17 hypothesis pBoot(κ)·B < q(κ) for F1, B = 1: smallest κ in {100, 200, …, 1500} where it holds",
  ((List.range 15).map fun i => 100 * (i + 1)).find? fun κ =>
    decide ((pBoot F1).eval κ * 1 < (F1.parameters κ).modulus))
