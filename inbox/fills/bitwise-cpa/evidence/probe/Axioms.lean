import TCSlib.Cryptography.Encryption.PublicKey.BitwiseCPA

/-! Axiom prints of the bitwise-cpa fill: the target, and the two corollaries that still depend on
the parallel `adaptive-cpa` target (`INDSecure.adaptive_cpa`). -/

#print axioms TCSlib.Cryptography.BitPublicKeyScheme.SingleBitSecure.bitwise_padded_cpa
#print axioms TCSlib.Cryptography.BitPublicKeyScheme.SingleBitSecure.bitwise_padded_adaptive_cpa
#print axioms TCSlib.Cryptography.BitPublicKeyScheme.SingleBitSecure.exists_adaptive_cpa
