import TCSlib.Cryptography.Encryption.PublicKey.NonMalleability.Indistinguishability
import TCSlib.Cryptography.Encryption.PublicKey.AdaptiveCPA.Games

/-! Escalation probe (c): the requested reader's one-line proof, with `outLens` sealed from the
start: it needs `outLens` definitionally, so it belongs in `PublicKey/OracleSecurity.lean`. -/
namespace TCSlib.Cryptography.Composability
open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games AdaptiveCPA

attribute [local irreducible] FixedLengthPKScheme.outLens

theorem decRng' (S : FixedLengthPKScheme) (n : ℕ) :
    (S.indSpec n).rng 0 = (Fin (S.msgLen.eval n + 1) → Bool) := by
  rw [S.indSpec_rng, S.outLens_zero]

-- the requested reader, proved by reading `outLens` (allowed only in its home file)
theorem decCast' (S : FixedLengthPKScheme) (atk : Attack) (b : Bool) (n : ℕ) (pk sk : List Bool)
    (c : (S.indSpec n).dom 0) (s : Option (Fin (S.ctLen.eval n) → Bool)) :
    S.indImpl atk b n pk sk 0 c s =
      if FixedLengthScheme.decOpen atk s.isSome && !decide (s = some (cast (S.indSpec_decDom n) c))
      then .pure (cast (decRng' S n).symm (FixedLengthScheme.decAnswer
        (decodeFin _ (S.dec (pairEncode sk (List.ofFn (cast (S.indSpec_decDom n) c)))))), s)
      else .pure (zeroBits _, s) := by
  simpa only [cast_eq] using S.indImpl_dec_onSpec atk b n pk sk c s

attribute [local irreducible] FixedLengthPKScheme.inLens
  FixedLengthPKScheme.indImpl FixedLengthPKScheme.nmDecrypt FixedLengthScheme.decAnswer
  FixedLengthScheme.decOpen castImpl padFin PolyExpr.eval acDin acDout

example (S : FixedLengthPKScheme) (b : Bool) (n : ℕ) (pk sk : List Bool)
    (x : Fin ((acDin S 0).eval n) → Bool) (st : Option (Fin (S.ctLen.eval n) → Bool)) :
    castImpl (ins := fun i => (acDin S i).eval n) (outs := fun i => (acDout S i).eval n)
      (S.indImpl .cca2 b n pk sk) 0 x st =
      .pure (padFin ((acDout S 0).eval n) (List.ofFn (S.nmDecrypt sk st
        (cast (S.indSpec_decDom n) (padFin (S.inLens n 0) (List.ofFn x))))), st) := by
  rw [castImpl_eq, decCast', FixedLengthScheme.decOpen_cca2, Bool.true_and,
    S.nmDecrypt_eq]
  by_cases hs : st = some (cast (S.indSpec_decDom n) (padFin (S.inLens n 0) (List.ofFn x)))
  · rw [if_neg (by simp [hs]), if_pos hs, OracleComp.pure_bind]
    congr 2
    rw [ofFn_zeroBits, ofFn_zeroBits, S.outLens_zero]
  · rw [if_pos (by simp [hs]), if_neg hs, OracleComp.pure_bind]
    dsimp only
    rw [ofFn_cast (S.outLens_zero n).symm]

end TCSlib.Cryptography.Composability
