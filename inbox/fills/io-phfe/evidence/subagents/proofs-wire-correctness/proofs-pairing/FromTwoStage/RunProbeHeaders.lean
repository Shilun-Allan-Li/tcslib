import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.SemiAdaptive.FromTwoStage

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption

open TCSlib.Cryptography.Pairing
open Complexity Turing TCSlib.Cryptography.Games

namespace TwoStage

/-- Proposed logical tape reader: concatenated original coin words recover both tapes.
This is only a native-search header, with no helper proof supplied. -/
theorem coinBlocks_ofFn_append (A : TwoStage) (kappa : ℕ)
    (r1 : A.first.Coins kappa) (r2 : A.second.Coins kappa) :
    (A.firstCoins kappa (List.ofFn r1 ++ List.ofFn r2),
      A.secondCoins kappa (List.ofFn r1 ++ List.ofFn r2)) = (r1, r2) := sorry

/-- Proposed exact real protocol law at a fixed tape and public key.
This is only a native-search header, with no helper proof supplied. -/
theorem simulate_toSA_real {C : FnClass} {S : FEScheme.Raw C}
    (A : TwoStage) (q : PolyExpr) (kappa : ℕ) (pp : PublicParams S.G kappa)
    (pk : S.MPK kappa pp) (msk : S.MSK kappa pp) (r : List Bool) :
    Prod.fst <$> simulate (S.realSAImpl kappa pp pk msk)
        ((A.toSA (S := S) q).run kappa pp pk r) none =
      let a := A.saCommitment C q kappa r
      (S.enc kappa pp pk a.publicInput a.privateInput).bind fun ct =>
      (List.mapM (fun j => S.keyGen kappa pp msk (a.functions j))
        (List.finRange (q.eval kappa))).bind fun keys =>
        .pure (A.second.distinguisherL kappa (S.viewWord a pp pk keys ct)
          (A.secondCoins kappa r)) := sorry

/-- Proposed exact ideal protocol law, retaining the simulator state through every key.
This is only a native-search header, with no helper proof supplied. -/
theorem simulate_toSA_ideal {C : FnClass} {S : FEScheme.Raw C}
    (Sim : FEScheme.Raw.SASimulator.Raw S) (A : TwoStage) (q : PolyExpr)
    (kappa : ℕ) (pp : PublicParams S.G kappa) (pk : S.MPK kappa pp)
    (st : Sim.St kappa pp) (r : List Bool) :
    Prod.fst <$> simulate (S.idealSAImpl Sim kappa pp)
        ((A.toSA (S := S) q).run kappa pp pk r) (st, none) =
      let a := A.saCommitment C q kappa r
      (Sim.enc kappa pp st a.publicInput).bind fun cst =>
      (List.mapM (m := StateT (Sim.St kappa pp) ProbComp)
        (fun j st' => Sim.key kappa pp st' a.publicInput (a.functions j)
          (C.eval kappa (S.cprm kappa pp) (a.functions j)
            a.publicInput a.privateInput))
        (List.finRange (q.eval kappa)) cst.2).bind fun keys =>
        .pure (A.second.distinguisherL kappa (S.viewWord a pp pk keys.1 cst.1)
          (A.secondCoins kappa r)) := sorry

end TwoStage
end TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption
