import TCSlib.Cryptography.LWE.BitNoise
/-! EF-D1-SR1 demonstration (evidence only): with `bitNoise` and `centeredNoise` sealed (as the
canonical seal of any consumer file does), the published readers `bitNoise_sample` and
`centeredNoise_sample`, stated at seeds of type `Fin _ → Bool`, cannot be used at a seed of type
`Coins`: both lines below fail exactly once each. -/
namespace TCSlib.Cryptography.LWE
attribute [local irreducible] bitNoise centeredNoise
example (t : ℕ) (f : (Fin t → Bool) → ℤ) (c : (bitNoise t f).Coins) :
    (bitNoise t f).sample c = f (cast (bitNoise_Coins t f) c) := bitNoise_sample t f c
example (t : ℕ) (c : (centeredNoise t).Coins) :
    (centeredNoise t).sample c = centeredValue t (cast (centeredNoise_Coins t) c) :=
  centeredNoise_sample t c
end TCSlib.Cryptography.LWE
