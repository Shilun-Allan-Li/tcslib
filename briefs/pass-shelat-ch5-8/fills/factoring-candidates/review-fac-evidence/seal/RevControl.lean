import TCSlib.Cryptography.Candidates.Factoring
/-! Review controls (fac): seven readings of foreign definitions by `rfl`/application, each closing
unsealed and failing under the review seal line (the same 65 names as the region seal). -/
namespace TCSlib.Cryptography.Candidates
open Complexity Turing NumberTheory Finset

section unsealed
example (inLen outLen m : PolyExpr) (A' : NUPPT) (n : ℕ) (ys : Fin (m.eval n) → Fin (outLen.eval n) → Bool) (r : A'.Coins n) (j : Fin (m.eval n)) :
    OneWay.yaoB inLen outLen m A' n ys r j = OneWay.padTrue (inLen.eval n)
      ((A'.runAt n (List.ofFn ((OneWay.blocksE (m.eval n) (outLen.eval n)).symm ys)) r).drop (j * inLen.eval n)) := rfl
example {A : NUPPT} (hA : A.Uniform) (n : ℕ) : A.advice n = [] := hA n
example (D : OneWay.YaoMachine.Data) (n : ℕ) : (OneWay.YaoMachine.ρP D).eval n = n * D.m.eval n + (D.m.eval n * D.inLen.eval n + D.A'.coinLen n) := rfl
example (A : NUPPT) (n : ℕ) : A.coinLen n = A.coins.eval n := rfl
example (n : ℕ) : (fmult.prod fmultBlocks).inLen.eval n = 4 * n ^ 3 * (2 * n) := rfl
example (k N : ℕ) : natToList k N = List.ofFn (natToBits k N) := rfl
example (m : ℕ) (z : DistinctPrimes m) : encodeDistinctPrimes m z = pairEncode (natToList m z.p) (natToList m z.q) := rfl
end unsealed

section sealed
attribute [local irreducible] _root_.Complexity.NUPPT.Uniform _root_.Complexity.NUPPT.advInput _root_.Complexity.NUPPT.coinLen _root_.Complexity.NUPPT.coinsCongr _root_.Complexity.NUPPT.coinsEquiv_ofPolyTime _root_.Complexity.NUPPT.inAdvice _root_.Complexity.NUPPT.inArg _root_.Complexity.NUPPT.inCoins _root_.Complexity.NUPPT.inParam _root_.Complexity.NUPPT.inverter _root_.Complexity.NUPPT.layout _root_.Complexity.NUPPT.ofPolyTime _root_.Complexity.NUPPT.ofPolyTimeUniform _root_.Complexity.NUPPT.output _root_.Complexity.NUPPT.runAt _root_.Complexity.NUPPT.runAtL _root_.Complexity.PolyExpr.normal _root_.Complexity.PolyTimeComputable _root_.Complexity.pairFstD _root_.Complexity.pairSndD _root_.TCSlib.Cryptography.Candidates.DistinctPrimes.default _root_.TCSlib.Cryptography.Candidates.DistinctPrimes.p _root_.TCSlib.Cryptography.Candidates.DistinctPrimes.q _root_.TCSlib.Cryptography.Candidates.decodeDistinctPrimes _root_.TCSlib.Cryptography.Candidates.encodeDistinctPrimes _root_.TCSlib.Cryptography.Candidates.leStr _root_.TCSlib.Cryptography.Candidates.mulStr _root_.TCSlib.Cryptography.Candidates.natToBits _root_.TCSlib.Cryptography.Candidates.natToList _root_.TCSlib.Cryptography.Candidates.primeStr _root_.TCSlib.Cryptography.Candidates.primesPairEquiv _root_.TCSlib.Cryptography.Collection.SampleClose _root_.TCSlib.Cryptography.Collection.index _root_.TCSlib.Cryptography.Collection.invProbAt _root_.TCSlib.Cryptography.FunFamily.Easy _root_.TCSlib.Cryptography.FunFamily.blocks _root_.TCSlib.Cryptography.FunFamily.invProbAt _root_.TCSlib.Cryptography.FunFamily.prod _root_.TCSlib.Cryptography.Negligible _root_.TCSlib.Cryptography.NumberTheory.chunk _root_.TCSlib.Cryptography.NumberTheory.listToNat _root_.TCSlib.Cryptography.NumberTheory.samplePrime _root_.TCSlib.Cryptography.NumberTheory.samplePrimeCoins _root_.TCSlib.Cryptography.OneWay.YaoMachine.adv _root_.TCSlib.Cryptography.OneWay.YaoMachine.advP _root_.TCSlib.Cryptography.OneWay.YaoMachine.ans _root_.TCSlib.Cryptography.OneWay.YaoMachine.ρP _root_.TCSlib.Cryptography.OneWay.blocksE _root_.TCSlib.Cryptography.OneWay.kkOf _root_.TCSlib.Cryptography.OneWay.padTrue _root_.TCSlib.Cryptography.OneWay.prodFun _root_.TCSlib.Cryptography.OneWay.roundSample _root_.TCSlib.Cryptography.OneWay.yaoB _root_.TCSlib.Cryptography.OneWay.yaoTry _root_.TCSlib.Cryptography.StatClose _root_.TCSlib.Cryptography.bitsEquiv _root_.TCSlib.Cryptography.bitsToNat _root_.TCSlib.Cryptography.invProb _root_.TCSlib.Cryptography.invProbOpt _root_.TCSlib.Cryptography.padFin _root_.TCSlib.Cryptography.padStr _root_.TCSlib.Cryptography.rejectionSample _root_.TCSlib.Cryptography.uexp _root_.TCSlib.Cryptography.uprob _root_.Turing.pairEncode
example (inLen outLen m : PolyExpr) (A' : NUPPT) (n : ℕ) (ys : Fin (m.eval n) → Fin (outLen.eval n) → Bool) (r : A'.Coins n) (j : Fin (m.eval n)) :
    OneWay.yaoB inLen outLen m A' n ys r j = OneWay.padTrue (inLen.eval n)
      ((A'.runAt n (List.ofFn ((OneWay.blocksE (m.eval n) (outLen.eval n)).symm ys)) r).drop (j * inLen.eval n)) := rfl
example {A : NUPPT} (hA : A.Uniform) (n : ℕ) : A.advice n = [] := hA n
example (D : OneWay.YaoMachine.Data) (n : ℕ) : (OneWay.YaoMachine.ρP D).eval n = n * D.m.eval n + (D.m.eval n * D.inLen.eval n + D.A'.coinLen n) := rfl
example (A : NUPPT) (n : ℕ) : A.coinLen n = A.coins.eval n := rfl
example (n : ℕ) : (fmult.prod fmultBlocks).inLen.eval n = 4 * n ^ 3 * (2 * n) := rfl
example (k N : ℕ) : natToList k N = List.ofFn (natToBits k N) := rfl
example (m : ℕ) (z : DistinctPrimes m) : encodeDistinctPrimes m z = pairEncode (natToList m z.p) (natToList m z.q) := rfl
end sealed

end TCSlib.Cryptography.Candidates
