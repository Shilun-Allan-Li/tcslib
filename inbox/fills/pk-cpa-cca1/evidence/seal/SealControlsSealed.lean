import TCSlib.Cryptography.Encryption.PrivateKey.OracleFromPRF

/-! Seal controls of the pk-cpa-cca1 fill (sealed with the full candidate list: every example
must fail): twelve readings through a definition body. -/

attribute [local irreducible] _root_.Complexity.NUPPT.coinLen _root_.Complexity.NUPPT.coinsCongr _root_.Complexity.NUPPT.coinsEquiv_ofPolyTimeUniform _root_.Complexity.NUPPT.ofPolyTimeUniform _root_.Complexity.NUPPT.runAt _root_.Complexity.NUPPT.toComp _root_.Complexity.NUPPT.toCompOn _root_.Complexity.NUPPT.toOracleAdversary _root_.Complexity.PolyExpr.eval _root_.Complexity.PolyTimeComputable _root_.Complexity.PrefixByLength.drop _root_.Complexity.pairFstD _root_.Complexity.pairSndD _root_.TCSlib.Cryptography.Composability.AdaptiveCPA.extTape _root_.TCSlib.Cryptography.Composability.AdaptiveCPA.msgOf _root_.TCSlib.Cryptography.Composability.FixedLengthScheme.INDSecure _root_.TCSlib.Cryptography.Composability.FixedLengthScheme.decAnswer _root_.TCSlib.Cryptography.Composability.FixedLengthScheme.decOpen _root_.TCSlib.Cryptography.Composability.FixedLengthScheme.encryptAt _root_.TCSlib.Cryptography.Composability.FixedLengthScheme.inLens _root_.TCSlib.Cryptography.Composability.FixedLengthScheme.indCodec _root_.TCSlib.Cryptography.Composability.FixedLengthScheme.indGame _root_.TCSlib.Cryptography.Composability.FixedLengthScheme.indImpl _root_.TCSlib.Cryptography.Composability.FixedLengthScheme.outLens _root_.TCSlib.Cryptography.Composability.FixedLengthScheme.splitHalf _root_.TCSlib.Cryptography.Composability.PRFGame.addPt _root_.TCSlib.Cryptography.Composability.PRFGame.atkOf _root_.TCSlib.Cryptography.Composability.PRFGame.ctOf _root_.TCSlib.Cryptography.Composability.PRFGame.ctP _root_.TCSlib.Cryptography.Composability.PRFGame.decAns _root_.TCSlib.Cryptography.Composability.PRFGame.decWF _root_.TCSlib.Cryptography.Composability.PRFGame.eImpl _root_.TCSlib.Cryptography.Composability.PRFGame.fImpl _root_.TCSlib.Cryptography.Composability.PRFGame.hitStar _root_.TCSlib.Cryptography.Composability.PRFGame.lazyImpl _root_.TCSlib.Cryptography.Composability.PRFGame.look _root_.TCSlib.Cryptography.Composability.PRFGame.ovr _root_.TCSlib.Cryptography.Composability.PRFGame.padAt _root_.TCSlib.Cryptography.Composability.PRFGame.pkDin _root_.TCSlib.Cryptography.Composability.PRFGame.pkDout _root_.TCSlib.Cryptography.Composability.PRFGame.pkHState _root_.TCSlib.Cryptography.Composability.PRFGame.pkHandler _root_.TCSlib.Cryptography.Composability.PRFGame.pkSeedTapes _root_.TCSlib.Cryptography.Composability.PRFGame.pkState _root_.TCSlib.Cryptography.Composability.PRFGame.qRed _root_.TCSlib.Cryptography.Composability.PRFGame.rStar _root_.TCSlib.Cryptography.EnsembleLemmas.blocks _root_.TCSlib.Cryptography.EnsembleLemmas.padL _root_.TCSlib.Cryptography.Games.Bridge.acceptGame _root_.TCSlib.Cryptography.Games.InteractiveHandler.advInput _root_.TCSlib.Cryptography.Games.InteractiveHandler.call _root_.TCSlib.Cryptography.Games.InteractiveHandler.finInput _root_.TCSlib.Cryptography.Games.InteractiveHandler.finish _root_.TCSlib.Cryptography.Games.InteractiveHandler.impl _root_.TCSlib.Cryptography.Games.InteractiveHandler.input _root_.TCSlib.Cryptography.Games.MachineCodec.encodeLog _root_.TCSlib.Cryptography.Games.OracleComp.AllOutputs _root_.TCSlib.Cryptography.Games.OracleComp.CostBoundedBy _root_.TCSlib.Cryptography.Games.OracleComp.bind _root_.TCSlib.Cryptography.Games.OracleComp.evalFn _root_.TCSlib.Cryptography.Games.ProbComp.expect _root_.TCSlib.Cryptography.Games.ProbComp.prob _root_.TCSlib.Cryptography.Games.ProbComp.sample _root_.TCSlib.Cryptography.Games.QueryImpl.comp _root_.TCSlib.Cryptography.Games.QueryImpl.ofComp _root_.TCSlib.Cryptography.Games.accept _root_.TCSlib.Cryptography.Games.advantage _root_.TCSlib.Cryptography.Games.bitCodec _root_.TCSlib.Cryptography.Games.buildComp _root_.TCSlib.Cryptography.Games.decodeBitMove _root_.TCSlib.Cryptography.Games.seedIn _root_.TCSlib.Cryptography.Games.simulate _root_.TCSlib.Cryptography.Games.zeroBits _root_.TCSlib.Cryptography.Negligible _root_.TCSlib.Cryptography.QueryTree.eval _root_.TCSlib.Cryptography.acceptProb _root_.TCSlib.Cryptography.decodeFin _root_.TCSlib.Cryptography.distAdv _root_.TCSlib.Cryptography.oracleDist _root_.TCSlib.Cryptography.padFin _root_.TCSlib.Cryptography.prfAdv _root_.TCSlib.Cryptography.prfDecFun _root_.TCSlib.Cryptography.prfEncFun _root_.TCSlib.Cryptography.prfScheme _root_.TCSlib.Cryptography.randomFunction _root_.Turing.pairEncode

open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games
open TCSlib.Cryptography.Composability TCSlib.Cryptography.Composability.PRFGame

-- Control 1: `PolyExpr.eval` through its body.
example (n : ℕ) : (PolyExpr.var.add PolyExpr.var).eval n = n + n := rfl
-- Control 2: `FixedLengthScheme.outLens` through its body.
example (S : FixedLengthScheme) (n : ℕ) : S.outLens n 0 = S.ctLen.eval n := rfl
-- Control 3: `OracleComp.CostBoundedBy` through its body.
example {ι : Type} {spec : OracleSpec ι} {α : Type} (i : ι) (x : spec.dom i)
    (k : spec.rng i → OracleComp spec α) (m : ℕ)
    (h : (OracleComp.query i x k).CostBoundedBy (fun _ => 1) m) : 1 ≤ m := h.1
-- Control 4: `simulate` through its body.
example {ι : Type} {spec : OracleSpec ι} {σ α : Type} (impl : QueryImpl spec σ unifSpec)
    (a : α) (s : σ) : simulate impl (OracleComp.pure a) s = .pure (a, s) := rfl
-- Control 5: `FixedLengthScheme.INDSecure` through its body.
example (S : FixedLengthScheme) (h : S.INDSecure .cpa) (A : NUPPT) (q : PolyExpr) :
    ∃ ε : ℕ → ℝ, Negligible ε ∧ ∀ n, advantage (S.indGame .cpa A (q.eval n) false n)
      (S.indGame .cpa A (q.eval n) true n) ≤ ε n := h A q
-- Control 6: the new helper `atkOf` through its body.
example : atkOf false = .cpa := rfl
-- Control 7: the new helper `fImpl` through its body.
example (ins outs : Fin 3 → ℕ) (d n : ℕ) (atk : Attack) (b : Bool)
    (f : (Fin n → Bool) → (Fin n → Bool)) (mm : Fin (ins 2) → Bool) (c : Fin d → Bool) :
    fImpl ins outs d n atk b f 2 mm (some c) = .pure (padFin _ (List.ofFn c), some c) := rfl
-- Control 8: the new helper `pkHandler` through its body.
example (q : PolyExpr) (atkBit b : Bool) : (pkHandler q atkBit b).finCall = .const 0 := rfl
-- Control 9: the new helper `pkHState` through its body.
example (q : PolyExpr) (atkBit b : Bool) (n j : ℕ) (o : Option (Fin (ctP.eval n) → Bool)) :
    pkHState q atkBit b n j o = pkState q n j o := rfl
-- Control 10: the new helper `look` through its body.
example (n d : ℕ) (b : Bool) (T : List ((Fin n → Bool) × (Fin n → Bool))) (bd : Bool)
    (x : Fin n → Bool) : look b ((T, none, bd) : LState n d) x = T.lookup x := rfl
-- Control 11: the new helper `addPt` through its body.
example (n d : ℕ) (b : Bool) (st : LState n d) (x y : Fin n → Bool) (hit : Bool) :
    (addPt b st x y hit).2.2 = (st.2.2 || hit) := rfl
-- Control 12: the new helper `lazyImpl` through its body.
example (ins outs : Fin 3 → ℕ) (d n : ℕ) (atk : Attack) (b : Bool) (mm : Fin (ins 2) → Bool)
    (T : List ((Fin n → Bool) × (Fin n → Bool))) (ml : List Bool) (c : Fin d → Bool) (bd : Bool) :
    lazyImpl ins outs d n atk b 2 mm (T, some (ml, c), bd) =
      .pure (padFin _ (List.ofFn c), (T, some (ml, c), bd)) := rfl
