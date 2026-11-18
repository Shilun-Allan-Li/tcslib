import TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.DecryptFormula

/-! Negative control for the owner `GSW/Scheme.lean`, whose `decrypt` the fill reads only through
`decrypt_eq_decode_dotProduct`: exactly one unfolding of `decrypt` by `rfl`. Passes unsealed;
must fail exactly once under every seal. -/

open TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW in
theorem ctl_unfold_decrypt (P : Parameters) (s : Fin P.lwe.dimension → ZMod P.lwe.modulus)
    (C : Ciphertext P) :
    decrypt P s C =
      TCSlib.Cryptography.Encryption.PublicKey.Regev.decrypt P.lwe s (Fin.init (decryptColumn P C), decryptColumn P C (Fin.last _)) := rfl
