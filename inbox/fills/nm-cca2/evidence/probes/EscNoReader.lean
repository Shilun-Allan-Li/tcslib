import TCSlib.Cryptography.Encryption.PublicKey.NonMalleability.Indistinguishability
import TCSlib.Cryptography.Encryption.PublicKey.AdaptiveCPA.Games

/-! Escalation probe (a): the obligation with only the published readers, `outLens` sealed. -/
namespace TCSlib.Cryptography.Composability
open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games AdaptiveCPA

attribute [local irreducible] FixedLengthPKScheme.outLens FixedLengthPKScheme.inLens
  FixedLengthPKScheme.indImpl FixedLengthPKScheme.nmDecrypt FixedLengthScheme.decAnswer
  FixedLengthScheme.decOpen castImpl padFin PolyExpr.eval acDin acDout

theorem ofFn_congr_len {a b : ℕ} (f : Fin a → Bool) (g : Fin b → Bool) (hab : a = b)
    (hfg : HEq f g) : List.ofFn f = List.ofFn g := by
  subst hab; cases hfg; rfl

example (S : FixedLengthPKScheme) (b : Bool) (n : ℕ) (pk sk : List Bool)
    (x : Fin ((acDin S 0).eval n) → Bool) (st : Option (Fin (S.ctLen.eval n) → Bool)) :
    castImpl (ins := fun i => (acDin S i).eval n) (outs := fun i => (acDout S i).eval n)
      (S.indImpl .cca2 b n pk sk) 0 x st =
      .pure (padFin ((acDout S 0).eval n) (List.ofFn (S.nmDecrypt sk st
        (cast (S.indSpec_decDom n) (padFin (S.inLens n 0) (List.ofFn x))))), st) := by
  rw [castImpl_eq, S.indImpl_dec_onSpec, FixedLengthScheme.decOpen_cca2, Bool.true_and,
    S.nmDecrypt_eq]
  by_cases hs : st = some (cast (S.indSpec_decDom n) (padFin (S.inLens n 0) (List.ofFn x)))
  · rw [if_neg (by simp [hs]), if_pos hs, OracleComp.pure_bind]
    congr 2
    rw [ofFn_zeroBits, ofFn_zeroBits, S.outLens_zero]
  · rw [if_pos (by simp [hs]), if_neg hs, OracleComp.pure_bind]
    congr 3
    refine ofFn_congr_len _ _ (S.outLens_zero n) ?_
    -- The remaining goal relates `decAnswer …` at `Fin (S.outLens n 0) → Bool` (the published
    -- reader's typing) to the same term at `Fin (S.msgLen.eval n + 1) → Bool`; with `outLens`
    -- sealed no published reader closes it.
    trace_state
    exact HEq.rfl

end TCSlib.Cryptography.Composability
