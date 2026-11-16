import TCSlib.Cryptography.AdvancedEncryption
set_option autoImplicit false
attribute [local irreducible] TCSlib.Cryptography.AdvancedEncryption.IdentityBased.IBEScheme.Correct
open TCSlib.Cryptography.AdvancedEncryption.IdentityBased
-- positive control: the same through the published reader passes
example (S : IBEScheme) (h : S.Correct) : S.Correct := by
  rw [IBEScheme.correct_iff] at h ⊢
  intro κ id m
  exact h κ id m
