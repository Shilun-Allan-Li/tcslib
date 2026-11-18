import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.SemiAdaptive.FromTwoStage

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption

open TCSlib.Cryptography.Pairing
open Complexity Turing TCSlib.Cryptography.Games

namespace TwoStage

/-- Proposed logical continuation law after a successful challenge. Existing history
payloads are retained, and only the remaining committed keys are sampled in order.
This file supplies a native-search statement only, not its proof. -/
theorem simulate_saKeys_real {C : FnClass} {S : FEScheme.Raw C}
    (A : TwoStage) (q : PolyExpr) (kappa : ℕ) (pp : PublicParams S.G kappa)
    (pk : S.MPK kappa pp) (msk : S.MSK kappa pp) (r : List Bool)
    (e : Sigma fun i => (S.saSpec kappa).dom i × (S.saSpec kappa).rng i)
    (es : QueryLog (S.saSpec kappa))
    (ctBits : Fin (S.ctLen.eval kappa) → Bool) (ch : SAChallenge C kappa)
    (hct : S.saCTPayload kappa e.1 e.2.2 = some ctBits)
    (hlen : es.length ≤ q.eval kappa) :
    let a := A.saCommitment C q kappa r
    Prod.fst <$> simulate (S.realSAImpl kappa pp pk msk)
        (buildComp (A.saNext (S := S) q kappa pp pk r) false
          (q.eval kappa - es.length) (e :: es)) (some ch) =
      (List.mapM (fun j => S.keyGen kappa pp msk (a.functions j))
        ((List.finRange (q.eval kappa)).drop es.length)).bind fun keys =>
        .pure (A.second.distinguisherL kappa
          (S.viewWordBits a pp (S.encMPK kappa pp pk)
            ((es.filterMap fun entry => S.saSKPayload kappa entry.1 entry.2.2) ++
              keys.map (S.encSK kappa pp)) ctBits)
          (A.secondCoins kappa r)) := sorry

end TwoStage
end TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption
