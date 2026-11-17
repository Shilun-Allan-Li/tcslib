import TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW
import TCSlib.Cryptography.LWE

/-! Probe P8 (gsw-6b statements, check 7): the asymptotic statements and `ofFamily`.
* Two sample families: `Fc` (constant parameters `n = 1`, `m = 2`, `q = 5`, `ℓ = 3`, noise `±1`) and `F1`
  (`n = κ + 1`, `m = 4(κ+2)² + 2κ`, `q = 2^(κ+2)`, `ℓ = κ + 2`).
* Every asymptotic definition and statement (A1, A3, `WeakCircularSecureFamily` and its reader = r3's A2,
  `ReductionEfficient`, `LeveledReductionEfficient`, `RatioBounded`, G16, G17 pure and leveled) is
  instantiated at both families (and `L = var + 1` levels): each `example`/`#check` elaborates.
* `ofFamily`'s readers `Parameters.ofFamily_lwe`, `Parameters.ofFamily_width` used as stated, and the
  numeric values of `(ofFamily F κ).columns`; `pBoot` and its reader `pBoot_eq` evaluate.
* `Fc.RatioBounded (fun _ => 1) (.const 5)` is **proved** through the reader `ratioBounded_iff` (and
  `decide` for the noise bound), so the ratio predicate is satisfiable.
-/

open TCSlib.Cryptography
open TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW
open Complexity

namespace P8

def χ1 : LWE.Noise := ⟨Fin 3, fun i => (i.val : ℤ) - 1⟩

theorem χ1_bounded : χ1.Bounded 1 := by
  rw [LWE.Noise.bounded_iff]
  decide

def Fc : LWE.Family where
  parameters _ := ⟨1, 2, 5, by decide⟩
  noise _ := χ1
  dimensionBound := .const 1
  samplesBound := .const 2
  residueBits := .const 3
  dimension_le _ := le_rfl
  samples_le _ := le_rfl
  modulus_le_pow _ := by show 5 ≤ 2 ^ 3; decide

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

/-- The ratio predicate holds for `Fc` with `B = 1`, `p = 5`. -/
theorem Fc_ratio : Fc.RatioBounded (fun _ => 1) (.const 5) := by
  rw [LWE.Family.ratioBounded_iff]
  exact fun _ => ⟨χ1_bounded, le_refl _⟩

/-! ### `ofFamily` through its readers -/

example (κ : ℕ) : (Parameters.ofFamily Fc κ).lwe = Fc.parameters κ := Parameters.ofFamily_lwe Fc κ
example (κ : ℕ) : (Parameters.ofFamily F1 κ).width = F1.residueBits.eval κ :=
  Parameters.ofFamily_width F1 κ
example : pBoot F1 = .mul (.mul (.mul (.mul (.const (2 ^ 70)) F1.residueBits)
      (.pow (.mul (.add F1.dimensionBound (.const 1)) F1.residueBits) 19))
    (.pow (.add (.add F1.residueBits (.mul (.add F1.dimensionBound (.const 1)) F1.residueBits))
      (.const 3)) 4)) F1.samplesBound := pBoot_eq F1

/-! ### Every asymptotic definition and statement elaborates at both families -/

section Inst
variable (F : LWE.Family)
example : Prop := WeakCircularSecureFamily Fc
example : Prop := WeakCircularSecureFamily F1
example : Prop := ReductionEfficient Fc
example : Prop := LeveledReductionEfficient F1 (.add .var (.const 1))
example : Prop := LWE.Family.RatioBounded F1 (fun κ => κ + 1) (.mul .var .var)
example (h : WeakCircularSecureFamily F1) (D : NUPPT) :=
  (weakCircularSecureFamily_iff F1).1 h D
end Inst

#check @indCPA_of_dlweAssumption Fc
#check @indCPA_of_dlweAssumption F1
#check @leveledINDCPA_of_dlweAssumption F1 (.add .var (.const 1))
#check @bootRatio_le_poly F1 (fun _ => 1) 3
#check @decrypt_fheEval_of_ratio Fc (fun _ => 1) 0 χ1_bounded
#check @decrypt_leveledEval_of_ratio F1 (fun _ => 1) 2 χ1_bounded
#check (encodeFheView (Parameters.ofFamily Fc 0))
#check (encodeLeveledView (Parameters.ofFamily F1 1) 2)

end P8

open P8 in
#eval ((Parameters.ofFamily Fc 0).columns, (Parameters.ofFamily F1 0).columns,
  (Parameters.ofFamily F1 5).columns, (Parameters.ofFamily F1 5).lwe.modulus)
open P8 in
#eval ((List.range 4).map fun κ => (pBoot F1).eval κ)
open P8 in
#eval ((pBoot Fc).eval 0, decide ((pBoot Fc).eval 0 = 2 ^ 70 * 3 * 6 ^ 19 * (3 + 6 + 3) ^ 4 * 2))
#print axioms P8.Fc_ratio
