import TCSlib.Cryptography.LWE.Efficient
/-! EF-D1-SR1 probe (evidence only, outside the library). The two readers proposed for
`LWE/BitNoise.lean` are stated here exactly as proposed, proved by `rfl` (they would be readers in
their owner's file, where `rfl` is allowed). With them, `CenteredSampleEq T` holds for every `T`,
so `noise_efficient_centeredNoise` and `EfficientFamily.ofDyadic` become unconditional, and the
example with `χ = centeredNoise 1` is built. -/
namespace TCSlib.Cryptography.LWE

open Complexity

/-- (proposed for `LWE/BitNoise.lean`) A sample of `bitNoise t f` at a seed of type `Coins` is
`f` of the seed read through `bitNoise_Coins`. -/
theorem bitNoise_sample_cast' (t : ℕ) (f : (Fin t → Bool) → ℤ) (c : (bitNoise t f).Coins) :
    (bitNoise t f).sample c = f (cast (bitNoise_Coins t f) c) := rfl

/-- (proposed for `LWE/BitNoise.lean`) A sample of `centeredNoise t` at a seed of type `Coins` is
`centeredValue t` of the seed read through `centeredNoise_Coins`. -/
theorem centeredNoise_sample_cast' (t : ℕ) (c : (centeredNoise t).Coins) :
    (centeredNoise t).sample c = centeredValue t (cast (centeredNoise_Coins t) c) := rfl

theorem centeredSampleEq_all (T : PolyExpr) : CenteredSampleEq T :=
  (centeredSampleEq_iff T).2 fun κ c => centeredNoise_sample_cast' _ c

/-- The instance the brief proposes: `n = κ + 1`, `m = 2(κ + 1)²`, `q = 2^{κ+1}`,
`χ = centeredNoise 1`. -/
def dyadicExampleOne : EfficientFamily :=
  EfficientFamily.ofDyadic (.add .var (.const 1)) (.mul (.const 2) (.pow (.add .var (.const 1)) 2))
    (.add .var (.const 1)) (.const 1)
    (fun κ => by rw [PolyExpr.eval_add, PolyExpr.eval_const]; exact Nat.le_add_left 1 _)
    (centeredSampleEq_all _)

example (κ : ℕ) : dyadicExampleOne.noise κ = centeredNoise 1 := by
  show centeredNoise ((PolyExpr.const 1).eval κ) = centeredNoise 1
  rw [PolyExpr.eval_const]

#print axioms dyadicExampleOne

end TCSlib.Cryptography.LWE
