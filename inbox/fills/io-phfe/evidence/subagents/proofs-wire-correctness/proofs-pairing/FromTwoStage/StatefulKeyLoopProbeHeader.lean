import TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption.SemiAdaptive.FromTwoStage

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption

open TCSlib.Cryptography.Pairing
open Complexity Turing TCSlib.Cryptography.Games

namespace TwoStage

/-- Logical correspondence for the remaining committed key loop, including its final state.
The one-query law relates an existing handler to an abstract stateful key callback.
No implementation, sampler, adversary or runtime interface is constructed here. -/
theorem simulate_saKeys_stateful {C : FnClass} {S : FEScheme.Raw C}
    (A : TwoStage) (q : PolyExpr) (kappa : ℕ) (pp : PublicParams S.G kappa)
    (pk : S.MPK kappa pp) (r : List Bool) {sigma tau : Type}
    (impl : QueryImpl (S.saSpec kappa) tau unifSpec)
    (stateMap : sigma → tau)
    (key : (Fin (C.fnLen.eval kappa) → Bool) →
      StateT sigma ProbComp (S.SK kappa pp))
    (hkey : ∀ (f : Fin (C.fnLen.eval kappa) → Bool) (st : sigma),
      impl 1 f (stateMap st) =
        (key f st).bind fun ks =>
          .pure (S.saSKAnswer kappa pp (some ks.1), stateMap ks.2))
    (e : Sigma fun i => (S.saSpec kappa).dom i × (S.saSpec kappa).rng i)
    (es : QueryLog (S.saSpec kappa))
    (ctBits : Fin (S.ctLen.eval kappa) → Bool) (st : sigma)
    (hct : S.saCTPayload kappa e.1 e.2.2 = some ctBits)
    (hlen : es.length ≤ q.eval kappa) :
    let a := A.saCommitment C q kappa r
    simulate impl
        (buildComp (A.saNext (S := S) q kappa pp pk r) false
          (q.eval kappa - es.length) (e :: es)) (stateMap st) =
      ((List.mapM (m := StateT sigma ProbComp)
        (fun j => key (a.functions j))
        ((List.finRange (q.eval kappa)).drop es.length)).run st).bind fun keys =>
        .pure (A.second.distinguisherL kappa
          (S.viewWordBits a pp (S.encMPK kappa pp pk)
            ((es.filterMap fun entry => S.saSKPayload kappa entry.1 entry.2.2) ++
              keys.1.map (S.encSK kappa pp)) ctBits)
          (A.secondCoins kappa r), stateMap keys.2) := sorry

end TwoStage
end TCSlib.Cryptography.AdvancedEncryption.FunctionalEncryption
