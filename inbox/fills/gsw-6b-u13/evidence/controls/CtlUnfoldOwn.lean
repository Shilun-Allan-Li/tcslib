import TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW.DecryptFormula

/-! Negative liveness control for the owner `GSW/DecryptFormula.lean`: exactly one unfolding of
its definition `decConstants` by `rfl`. Passes unsealed; must fail exactly once under every seal. -/

open TCSlib.Cryptography.AdvancedEncryption.Homomorphic.GSW in
theorem ctl_unfold_decConstants (P : Parameters) (C : Ciphertext P) :
    decConstants P C = Matrix.vecMul (decryptColumn P C) (gadget P) := rfl
