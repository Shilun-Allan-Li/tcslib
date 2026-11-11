import TCSlib.Cryptography.Encryption.PublicKey.BitwiseCPA

/-! Seal controls of the bitwise-cpa fill (sealed with the full candidate list: every example
must fail): eight readings through a definition body. -/

attribute [local irreducible] _root_.Complexity.NUPPT.Uniform _root_.Complexity.NUPPT.coinLen _root_.Complexity.NUPPT.coinsCongr _root_.Complexity.NUPPT.distinguisherL _root_.Complexity.NUPPT.ofPolyTimeUniform _root_.Complexity.NUPPT.output _root_.Complexity.NUPPT.runAt _root_.Complexity.NUPPT.runAtL _root_.Complexity.NUPPT.toCompOn _root_.Complexity.PolyExpr.eval _root_.Complexity.PolyTimeComputable _root_.Complexity.pairFstD _root_.Complexity.pairSndD _root_.TCSlib.Cryptography.BitPublicKeyScheme.SingleBitSecure _root_.TCSlib.Cryptography.BitPublicKeyScheme.bitwise _root_.TCSlib.Cryptography.BitPublicKeyScheme.bitwiseEncCoins _root_.TCSlib.Cryptography.BitPublicKeyScheme.bitwiseEncFun _root_.TCSlib.Cryptography.BitPublicKeyScheme.pkEncDist _root_.TCSlib.Cryptography.Composability.BitwiseSim.plantAns _root_.TCSlib.Cryptography.Composability.BitwiseSim.plantOut _root_.TCSlib.Cryptography.Composability.BitwiseSim.plantTuple _root_.TCSlib.Cryptography.Composability.BitwiseSim.qDin _root_.TCSlib.Cryptography.Composability.BitwiseSim.qDout _root_.TCSlib.Cryptography.Composability.ChallengeSim.chRun _root_.TCSlib.Cryptography.Composability.ChallengeSim.firstQ _root_.TCSlib.Cryptography.Composability.ChallengeSim.recAdvIn _root_.TCSlib.Cryptography.Composability.FixedLengthPKScheme.INDSecure _root_.TCSlib.Cryptography.Composability.FixedLengthPKScheme.inLens _root_.TCSlib.Cryptography.Composability.FixedLengthPKScheme.indCodec _root_.TCSlib.Cryptography.Composability.FixedLengthPKScheme.indGame _root_.TCSlib.Cryptography.Composability.FixedLengthPKScheme.indImpl _root_.TCSlib.Cryptography.Composability.FixedLengthPKScheme.outLens _root_.TCSlib.Cryptography.Composability.FixedLengthScheme.decAnswer _root_.TCSlib.Cryptography.Composability.FixedLengthScheme.decOpen _root_.TCSlib.Cryptography.Composability.FixedLengthScheme.splitHalf _root_.TCSlib.Cryptography.Composability.padCt _root_.TCSlib.Cryptography.Games.Bridge.acceptGame _root_.TCSlib.Cryptography.Games.OracleComp.bind _root_.TCSlib.Cryptography.Games.PolyHandler.advInput _root_.TCSlib.Cryptography.Games.PolyHandler.answer _root_.TCSlib.Cryptography.Games.PolyHandler.impl _root_.TCSlib.Cryptography.Games.PolyHandler.input _root_.TCSlib.Cryptography.Games.PolyHandler.result _root_.TCSlib.Cryptography.Games.ProbComp.expect _root_.TCSlib.Cryptography.Games.ProbComp.prob _root_.TCSlib.Cryptography.Games.ProbComp.sample _root_.TCSlib.Cryptography.Games.accept _root_.TCSlib.Cryptography.Games.advantage _root_.TCSlib.Cryptography.Games.bitCodec _root_.TCSlib.Cryptography.Games.decodeBitMove _root_.TCSlib.Cryptography.Games.seedIn _root_.TCSlib.Cryptography.Games.simulate _root_.TCSlib.Cryptography.Games.zeroBits _root_.TCSlib.Cryptography.Negligible _root_.TCSlib.Cryptography.PrivateKeyScheme.encodeList _root_.TCSlib.Cryptography.PublicKeyScheme.padded _root_.TCSlib.Cryptography.acceptProb _root_.TCSlib.Cryptography.blockEncFun _root_.TCSlib.Cryptography.blockState _root_.TCSlib.Cryptography.coinBlock _root_.TCSlib.Cryptography.coinBlocks _root_.TCSlib.Cryptography.decodeFin _root_.TCSlib.Cryptography.distAdv _root_.TCSlib.Cryptography.padFin _root_.Turing.pairDecode _root_.Turing.pairEncode

open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games
open TCSlib.Cryptography.Composability TCSlib.Cryptography.Composability.ChallengeSim
open TCSlib.Cryptography.Composability.BitwiseSim

-- Control 1: `FixedLengthPKScheme.inLens` through its body.
example (S : FixedLengthPKScheme) (n : ℕ) :
    S.inLens n 1 = S.msgLen.eval n + S.msgLen.eval n := rfl
-- Control 2: `FixedLengthPKScheme.outLens` through its body.
example (S : FixedLengthPKScheme) (n : ℕ) : S.outLens n 1 = S.ctLen.eval n := rfl
-- Control 3: `PolyExpr.eval` through its body.
example (n : ℕ) : (PolyExpr.const 3).eval n = 3 := rfl
-- Control 4: `padCt` through its body.
example (L : ℕ) (c : List Bool) :
    padCt L c = pairEncode c (List.replicate (L - (2 * c.length + 2)) true) := rfl
-- Control 5: `seedIn` through its body.
example (n : ℕ) (z ω : List Bool) :
    seedIn n z ω = pairEncode (List.replicate n true) (pairEncode z ω) := rfl
-- Control 6: the published helper `chRun` through its body.
example {ins outs : Fin 2 → ℕ} (g : (Fin (ins 1) → Bool) → List Bool) (a : ℕ)
    (s : Option (Fin (outs 1) → Bool)) : chRun g (.pure a) s = (a, s) := rfl
-- Control 7: the new helper `qDin` through its body.
example (Lc Lq : PolyExpr) : qDin Lc Lq 1 = Lq := rfl
-- Control 8: the new helper `plantAns` through its body.
example (Enc : NUPPT) (L : PolyExpr) (w : List Bool) :
    plantAns Enc L w = padCt (L.eval (pairFstD (pairFstD w)).length) (plantTuple Enc w) := rfl
