import TCSlib.Cryptography.Encryption.PublicKey.OracleSecurity

/-! Seal controls of the padded-cpa fill (sealed with the full candidate list: every example must fail): seven readings through a definition body. -/

attribute [local irreducible] _root_.Complexity.NUPPT.coinLen _root_.Complexity.NUPPT.coinsCongr _root_.Complexity.NUPPT.distinguisherL _root_.Complexity.NUPPT.runAt _root_.Complexity.NUPPT.toCompOn _root_.Complexity.PolyExpr.eval _root_.Complexity.PolyTimeComputable _root_.Complexity.pairFstD _root_.Complexity.pairSndD _root_.TCSlib.Cryptography.BitPublicKeyScheme.SingleBitSecure _root_.TCSlib.Cryptography.BitPublicKeyScheme.pkEncDist _root_.TCSlib.Cryptography.Composability.ChallengeSim.chRun _root_.TCSlib.Cryptography.Composability.ChallengeSim.firstQ _root_.TCSlib.Cryptography.Composability.ChallengeSim.recAdvIn _root_.TCSlib.Cryptography.Composability.ChallengeSim.recDin _root_.TCSlib.Cryptography.Composability.ChallengeSim.recDout _root_.TCSlib.Cryptography.Composability.ChallengeSim.recHandler _root_.TCSlib.Cryptography.Composability.ChallengeSim.recOut _root_.TCSlib.Cryptography.Composability.FixedLengthScheme.splitHalf _root_.TCSlib.Cryptography.Games.Bridge.acceptGame _root_.TCSlib.Cryptography.Games.OracleComp.bind _root_.TCSlib.Cryptography.Games.PolyHandler.advInput _root_.TCSlib.Cryptography.Games.PolyHandler.answer _root_.TCSlib.Cryptography.Games.PolyHandler.impl _root_.TCSlib.Cryptography.Games.PolyHandler.input _root_.TCSlib.Cryptography.Games.PolyHandler.result _root_.TCSlib.Cryptography.Games.ProbComp.expect _root_.TCSlib.Cryptography.Games.ProbComp.prob _root_.TCSlib.Cryptography.Games.ProbComp.sample _root_.TCSlib.Cryptography.Games.accept _root_.TCSlib.Cryptography.Games.advantage _root_.TCSlib.Cryptography.Games.bitCodec _root_.TCSlib.Cryptography.Games.seedIn _root_.TCSlib.Cryptography.Games.simulate _root_.TCSlib.Cryptography.Games.zeroBits _root_.TCSlib.Cryptography.Negligible _root_.TCSlib.Cryptography.acceptProb _root_.TCSlib.Cryptography.distAdv _root_.TCSlib.Cryptography.padFin _root_.Turing.pairDecode _root_.Turing.pairEncode

open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games
open TCSlib.Cryptography.Composability TCSlib.Cryptography.Composability.ChallengeSim

-- Control 1: `PolyExpr.eval` through its body.
example (n : ℕ) : (PolyExpr.const 3).eval n = 3 := rfl
-- Control 2: `zeroBits` through its body.
example (d : ℕ) (j : Fin d) : zeroBits d j = false := rfl
-- Control 3: `padFin` through its body.
example (ℓ : ℕ) (w : List Bool) (i : Fin ℓ) : padFin ℓ w i = w.getD i false := rfl
-- Control 4: `seedIn` through its body.
example (n : ℕ) (z ω : List Bool) :
    seedIn n z ω = pairEncode (List.replicate n true) (pairEncode z ω) := rfl
-- Control 5: `simulate` through its body.
example {ι σ α : Type} {spec : OracleSpec ι} (impl : QueryImpl spec σ unifSpec) (a : α) (s : σ) :
    simulate impl (.pure a) s = .pure (a, s) := rfl
-- Control 6: the helper `chRun` through its body.
example {ins outs : Fin 2 → ℕ} (g : (Fin (ins 1) → Bool) → List Bool) (a : ℕ)
    (s : Option (Fin (outs 1) → Bool)) : chRun g (.pure a) s = (a, s) := rfl
-- Control 7: the helper `recDin` through its body.
example (L : PolyExpr) : recDin L 1 = .const 2 := rfl
