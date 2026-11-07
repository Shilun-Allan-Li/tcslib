import TCSlib.Cryptography.Candidates.Rabin
import TCSlib.Cryptography.Candidates.ElGamal
import TCSlib.Cryptography.Candidates.DiscreteLogHardcore
/-! S1 seal controls: thirteen readings of foreign definitions by their bodies (C1–C13), each
closing unsealed (namespace `S1Unsealed`) and failing under the union of the S1 seals (namespace
`S1Sealed`, 89 names; `PolyExpr.eval` and `glNeed` left unsealed). -/
open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Candidates NumberTheory

namespace S1Unsealed
-- C1 natToList by its body
example (k N : ℕ) : natToList k N = List.ofFn (natToBits k N) := rfl
-- C2 listToNat by its body
example (w : List Bool) : listToNat w = w.foldl (fun a c => 2 * a + if c then 1 else 0) 0 := rfl
-- C3 rejectBlocksL by its body
example (E : ℕ → Prop) [DecidablePred E] (k B T : ℕ) (r : List Bool) :
    rejectBlocksL E k B T r = (List.range T).findSome? fun t =>
      if E (listToNat ((r.drop (t * B)).take k)) then some (listToNat ((r.drop (t * B)).take k))
      else none := rfl
-- C4 StatClose by its body
example (X Y : Fin 2 → ℕ) (δ : ℝ) :
    StatClose X Y δ ↔ ∀ T : ℕ → Prop, |uprob (fun s => T (X s)) - uprob (fun t => T (Y t))| ≤ δ :=
  Iff.rfl
-- C5 uexp by its body
example (f : Fin 3 → ℝ) : uexp f = (∑ a, f a) / Fintype.card (Fin 3) := rfl
-- C6 PushesUniform by its body
example (π : Fin 2 → Fin 2) :
    HardcoreBit.PushesUniform π ↔ ∀ F : Fin 2 → ℝ, uexp (fun ω => F (π ω)) = uexp F := Iff.rfl
-- C7 PolyTimeComputable by its body
example (f : List Bool → List Bool) : PolyTimeComputable f ↔
    ∃ (M : FinTM Bool) (C c : ℕ), M.ComputesFunInTime f fun n => C * (n + 1) ^ c := Iff.rfl
-- C8 sampleUnitL by its body
example (N k B T : ℕ) (r : List Bool) :
    sampleUnitL N k B T r = rejectBlocksL (fun v => v < N ∧ Nat.Coprime v N) k B T r := rfl
-- C9 subStr by its body
example (z : List Bool) : subStr z =
    natToList (pairFstD z).length (listToNat (pairFstD z) - listToNat (pairSndD z)) := rfl
-- C10 the repetition host's matcher against a local match on the same discriminant
example (o : Option ℕ) (a : ℕ → List Bool) (b : List Bool) :
    Complexity.polyTimeComputable_iterateFind.match_1 (fun _ => List Bool) o (fun i => a i) (fun _ => b) =
      (match o with | some i => a i | none => b) := rfl
-- C11 sampleBelowL by its body
example (m k B T : ℕ) (r : List Bool) : sampleBelowL m k B T r = (List.range T).findSome? fun t =>
    if listToNat ((r.drop (t * B)).take k) < m then some (listToNat ((r.drop (t * B)).take k))
    else none := rfl
-- C12 bitsToNat by its body
example (b : Fin 3 → Bool) :
    bitsToNat b = (List.ofFn b).foldl (fun a c => 2 * a + (if c then 1 else 0)) 0 := rfl
-- C13 mulStr by its body
example (z : List Bool) : mulStr z = natToList ((pairFstD z).length + (pairSndD z).length)
    (listToNat (pairFstD z) * listToNat (pairSndD z)) := rfl
end S1Unsealed

namespace S1Sealed
attribute [local irreducible] _root_.Complexity.NUPPT.Uniform _root_.Complexity.NUPPT.coinLen _root_.Complexity.NUPPT.coinsCongr _root_.Complexity.NUPPT.coinsEquivPoly _root_.Complexity.NUPPT.distinguisher _root_.Complexity.NUPPT.distinguisherL _root_.Complexity.NUPPT.inAdvice _root_.Complexity.NUPPT.inArg _root_.Complexity.NUPPT.inCoins _root_.Complexity.NUPPT.inParam _root_.Complexity.NUPPT.inverter _root_.Complexity.NUPPT.layout _root_.Complexity.NUPPT.ofPolyTime _root_.Complexity.NUPPT.ofPolyTimeUniform _root_.Complexity.NUPPT.output _root_.Complexity.NUPPT.runAt _root_.Complexity.NUPPT.runAtL _root_.Complexity.PolyTimeComputable _root_.Complexity.StateLoop.gstep _root_.Complexity.StateLoop.gstepBound _root_.Complexity.pairFstD _root_.Complexity.pairSndD _root_.Complexity.polyTimeComputable_iterateFind.match_1 _root_.TCSlib.Cryptography.Candidates.DistinctPrimes.default _root_.TCSlib.Cryptography.Candidates.DistinctPrimes.p _root_.TCSlib.Cryptography.Candidates.DistinctPrimes.q _root_.TCSlib.Cryptography.Candidates.ExpGroupGen.DLHard _root_.TCSlib.Cryptography.Candidates.ExpGroupGen.FullLengthExcept _root_.TCSlib.Cryptography.Candidates.ExpGroupGen.dlProb _root_.TCSlib.Cryptography.Candidates.ExpValid _root_.TCSlib.Cryptography.Candidates.SafePrimeValid _root_.TCSlib.Cryptography.Candidates.WellFormedIndex _root_.TCSlib.Cryptography.Candidates.addStr _root_.TCSlib.Cryptography.Candidates.decodeDistinctPrimes _root_.TCSlib.Cryptography.Candidates.divModStr _root_.TCSlib.Cryptography.Candidates.dlG _root_.TCSlib.Cryptography.Candidates.dlM _root_.TCSlib.Cryptography.Candidates.dlP _root_.TCSlib.Cryptography.Candidates.dlW _root_.TCSlib.Cryptography.Candidates.encodeDistinctPrimes _root_.TCSlib.Cryptography.Candidates.expCollection _root_.TCSlib.Cryptography.Candidates.expCollection_coinsEquiv _root_.TCSlib.Cryptography.Candidates.expCollection_domEquiv _root_.TCSlib.Cryptography.Candidates.expF _root_.TCSlib.Cryptography.Candidates.expOrd _root_.TCSlib.Cryptography.Candidates.expUnit _root_.TCSlib.Cryptography.Candidates.leStr _root_.TCSlib.Cryptography.Candidates.modExpStr _root_.TCSlib.Cryptography.Candidates.modulusBits _root_.TCSlib.Cryptography.Candidates.mulStr _root_.TCSlib.Cryptography.Candidates.natToBits _root_.TCSlib.Cryptography.Candidates.natToList _root_.TCSlib.Cryptography.Candidates.rejectBlocksL _root_.TCSlib.Cryptography.Candidates.rsaBlock _root_.TCSlib.Cryptography.Candidates.rsaSampleCoins _root_.TCSlib.Cryptography.Candidates.rsaTrials _root_.TCSlib.Cryptography.Candidates.sampleBelowL _root_.TCSlib.Cryptography.Candidates.samplePrimeL _root_.TCSlib.Cryptography.Candidates.sampleUnitL _root_.TCSlib.Cryptography.Candidates.sizeStr _root_.TCSlib.Cryptography.Candidates.subStr _root_.TCSlib.Cryptography.Candidates.unitSampleStr _root_.TCSlib.Cryptography.Candidates.xgcdStr _root_.TCSlib.Cryptography.Collection.SampleClose _root_.TCSlib.Cryptography.Collection.index _root_.TCSlib.Cryptography.FunFamily.blocks _root_.TCSlib.Cryptography.HardcoreBit.PushesUniform _root_.TCSlib.Cryptography.HardcoreBit.majority _root_.TCSlib.Cryptography.Negligible _root_.TCSlib.Cryptography.NumberTheory.QR _root_.TCSlib.Cryptography.NumberTheory.chunk _root_.TCSlib.Cryptography.NumberTheory.listToNat _root_.TCSlib.Cryptography.NumberTheory.samplePrime _root_.TCSlib.Cryptography.NumberTheory.samplePrimeCoins _root_.TCSlib.Cryptography.NumberTheory.sqTo _root_.TCSlib.Cryptography.StatClose _root_.TCSlib.Cryptography.acceptProb _root_.TCSlib.Cryptography.bitsEquiv _root_.TCSlib.Cryptography.bitsToNat _root_.TCSlib.Cryptography.decodeFin _root_.TCSlib.Cryptography.firstHit _root_.TCSlib.Cryptography.invProb _root_.TCSlib.Cryptography.padFin _root_.TCSlib.Cryptography.predProb _root_.TCSlib.Cryptography.rejectionSample _root_.TCSlib.Cryptography.splitCoins _root_.TCSlib.Cryptography.uexp _root_.TCSlib.Cryptography.uprob _root_.Turing.pairEncode
-- C1 natToList by its body
example (k N : ℕ) : natToList k N = List.ofFn (natToBits k N) := rfl
-- C2 listToNat by its body
example (w : List Bool) : listToNat w = w.foldl (fun a c => 2 * a + if c then 1 else 0) 0 := rfl
-- C3 rejectBlocksL by its body
example (E : ℕ → Prop) [DecidablePred E] (k B T : ℕ) (r : List Bool) :
    rejectBlocksL E k B T r = (List.range T).findSome? fun t =>
      if E (listToNat ((r.drop (t * B)).take k)) then some (listToNat ((r.drop (t * B)).take k))
      else none := rfl
-- C4 StatClose by its body
example (X Y : Fin 2 → ℕ) (δ : ℝ) :
    StatClose X Y δ ↔ ∀ T : ℕ → Prop, |uprob (fun s => T (X s)) - uprob (fun t => T (Y t))| ≤ δ :=
  Iff.rfl
-- C5 uexp by its body
example (f : Fin 3 → ℝ) : uexp f = (∑ a, f a) / Fintype.card (Fin 3) := rfl
-- C6 PushesUniform by its body
example (π : Fin 2 → Fin 2) :
    HardcoreBit.PushesUniform π ↔ ∀ F : Fin 2 → ℝ, uexp (fun ω => F (π ω)) = uexp F := Iff.rfl
-- C7 PolyTimeComputable by its body
example (f : List Bool → List Bool) : PolyTimeComputable f ↔
    ∃ (M : FinTM Bool) (C c : ℕ), M.ComputesFunInTime f fun n => C * (n + 1) ^ c := Iff.rfl
-- C8 sampleUnitL by its body
example (N k B T : ℕ) (r : List Bool) :
    sampleUnitL N k B T r = rejectBlocksL (fun v => v < N ∧ Nat.Coprime v N) k B T r := rfl
-- C9 subStr by its body
example (z : List Bool) : subStr z =
    natToList (pairFstD z).length (listToNat (pairFstD z) - listToNat (pairSndD z)) := rfl
-- C10 the repetition host's matcher against a local match on the same discriminant
example (o : Option ℕ) (a : ℕ → List Bool) (b : List Bool) :
    Complexity.polyTimeComputable_iterateFind.match_1 (fun _ => List Bool) o (fun i => a i) (fun _ => b) =
      (match o with | some i => a i | none => b) := rfl
-- C11 sampleBelowL by its body
example (m k B T : ℕ) (r : List Bool) : sampleBelowL m k B T r = (List.range T).findSome? fun t =>
    if listToNat ((r.drop (t * B)).take k) < m then some (listToNat ((r.drop (t * B)).take k))
    else none := rfl
-- C12 bitsToNat by its body
example (b : Fin 3 → Bool) :
    bitsToNat b = (List.ofFn b).foldl (fun a c => 2 * a + (if c then 1 else 0)) 0 := rfl
-- C13 mulStr by its body
example (z : List Bool) : mulStr z = natToList ((pairFstD z).length + (pairSndD z).length)
    (listToNat (pairFstD z) * listToNat (pairSndD z)) := rfl
end S1Sealed
