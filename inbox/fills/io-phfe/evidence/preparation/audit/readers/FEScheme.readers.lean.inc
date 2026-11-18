namespace FEScheme

variable {C : FnClass} (S : FEScheme C)

/-- The raw projection preserves the public group generator. -/
theorem toRaw_G : S.toRaw.G = S.G := rfl

/-- The raw projection preserves the class-parameter interpretation. -/
theorem toRaw_cprm : S.toRaw.cprm = S.cprm := rfl

/-- The raw projection preserves the master public-key family. -/
theorem toRaw_MPK : S.toRaw.MPK = S.MPK := rfl

/-- The raw projection preserves the master secret-key family. -/
theorem toRaw_MSK : S.toRaw.MSK = S.MSK := rfl

/-- The raw projection preserves the functional-key family. -/
theorem toRaw_SK : S.toRaw.SK = S.SK := rfl

/-- The raw projection preserves the ciphertext family. -/
theorem toRaw_CT : S.toRaw.CT = S.CT := rfl

/-- The raw projection preserves the successful decryption-output family. -/
theorem toRaw_DecOut : S.toRaw.DecOut = S.DecOut := rfl

/-- The raw projection preserves the interpretation of class values in the output group. -/
theorem toRaw_embed : S.toRaw.embed = S.embed := rfl

/-- The raw projection preserves the deterministic setup core. -/
theorem toRaw_setupCore : S.toRaw.setupCore = S.setupCore := rfl

/-- The raw projection preserves the deterministic encryption core. -/
theorem toRaw_encCore : S.toRaw.encCore = S.encCore := rfl

/-- The raw projection preserves the deterministic key-generation core. -/
theorem toRaw_keyCore : S.toRaw.keyCore = S.keyCore := rfl

/-- The raw projection preserves deterministic decryption, including its failure result. -/
theorem toRaw_dec : S.toRaw.dec = S.dec := rfl

/-- The raw projection preserves the master public-key encoding. -/
theorem toRaw_encMPK : S.toRaw.encMPK = S.encMPK := rfl

/-- The raw projection preserves the functional-key encoding. -/
theorem toRaw_encSK : S.toRaw.encSK = S.encSK := rfl

/-- The raw projection preserves the ciphertext encoding. -/
theorem toRaw_encCT : S.toRaw.encCT = S.encCT := rfl

end FEScheme
