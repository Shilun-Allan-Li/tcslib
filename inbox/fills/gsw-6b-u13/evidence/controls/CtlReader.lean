import TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.DecryptFormula

/-! Positive controls: the same facts through the published readers (`decConstants_eq`,
`decrypt_eq`). Pass unsealed and under every seal. -/

open TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW in
theorem ctl_reader_decConstants (P : Parameters) (C : Ciphertext P) :
    decConstants P C = Matrix.vecMul (decryptColumn P C) (gadget P) := decConstants_eq P C

open TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW in
theorem ctl_reader_decrypt (P : Parameters) (s : Fin P.lwe.dimension → ZMod P.lwe.modulus)
    (C : Ciphertext P) :
    decrypt P s C =
      TCSlib.Cryptography.Encryption.PublicKey.Regev.decrypt P.lwe s (Fin.init (decryptColumn P C), decryptColumn P C (Fin.last _)) :=
  decrypt_eq P s C
