import TCSlib.Cryptography.AdvancedEncryption
set_option autoImplicit false
attribute [local irreducible] TCSlib.Cryptography.AdvancedEncryption.IdentityBased.IBEScheme.Correct
open TCSlib.Cryptography.AdvancedEncryption.IdentityBased
-- negative control: `intro` through the sealed `Correct` must fail
example (S : IBEScheme) (h : S.Correct) : S.Correct := by
  intro κ id m
  exact h κ id m
