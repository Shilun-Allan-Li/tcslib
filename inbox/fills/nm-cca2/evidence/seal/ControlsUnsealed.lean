import TCSlib.Cryptography.Encryption.PublicKey.NonMalleability.Indistinguishability

set_option autoImplicit false
open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games
open TCSlib.Cryptography.Composability TCSlib.Cryptography.Composability.AdaptiveCPA
open TCSlib.Cryptography.Composability.NMCCA2

-- 1. `FixedLengthPKScheme.inLens` (OracleSecurity) through its body.
example (S : FixedLengthPKScheme) (n : ℕ) : S.inLens n 0 = S.ctLen.eval n := rfl
-- 2. `FixedLengthPKScheme.outLens` (OracleSecurity), the escalation's identification.
example (S : FixedLengthPKScheme) (n : ℕ) : S.outLens n 0 = S.msgLen.eval n + 1 := rfl
-- 3. `PolyExpr.eval` through its body (fails only in variant B).
example (n : ℕ) : (PolyExpr.const 3).eval n = 3 := rfl
-- 4. `Games.seedIn` through its body.
example (n : ℕ) (z ω : List Bool) :
    seedIn n z ω = pairEncode (List.replicate n true) (pairEncode z ω) := rfl
-- 5. `padFin` (Asymptotic.Adversary) through its body.
example : padFin 1 [true] 0 = true := rfl
-- 6. `AdaptiveCPA.acDin` through its body.
example (S : FixedLengthPKScheme) : acDin S 0 = S.ctLen := rfl
-- 7. the helper `NMCCA2.finU` (Forward) through its body.
example (w : List Bool) : finU w = pairFstD (pairFstD w) := rfl
-- 8. the helper `NMCCA2.fwdHandler` (Forward) through its body.
example {k : ℕ} (din dout : Fin k → PolyExpr) (sl : PolyExpr) (a : List Bool → List Bool)
    (ha : PolyTimeComputable a) (o f : PolyExpr) (r : List Bool → List Bool)
    (hr : PolyTimeComputable r) : (fwdHandler din dout sl a ha o f r hr).perCall = .const 1 := rfl
-- 9. the helper `NMCCA2.cntRead` (Decrypt) through its body.
example : cntRead [] = [] := rfl
-- 10. the helper `NMCCA2.decHandler` (Decrypt) through its body.
example (S : FixedLengthPKScheme) (ℓ : PolyExpr) (D : NUPPT) : (decHandler S ℓ D).finCall = ℓ := rfl
-- 11. the helper `NMCCA2.encHandler` (Encrypt) through its body.
example (S : FixedLengthPKScheme) : (encHandler S).finCall = .const 0 := rfl
-- 12. the helper `NMCCA2.guessBit` (Encrypt) through its body.
example : guessBit [] = true := rfl
-- 13. the owned file's `nmCodec` through its body.
example (S : FixedLengthPKScheme) (n ℓ : ℕ) :
    S.nmCodec n ℓ = bitCodec (S.inLens n) (S.outLens n) (ℓ * S.ctLen.eval n) := rfl
