import TCSlib.Cryptography.Encryption.PublicKey.NonMalleability.Simulation

set_option autoImplicit false
open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games
open TCSlib.Cryptography.Composability TCSlib.Cryptography.Composability.NMSim

-- 1. `PolyExpr.eval` through its body (fails only in variant B).
example (n : ℕ) : (PolyExpr.const 3).eval n = 3 := rfl
-- 2. `FixedLengthPKScheme.NMSecure` (Indistinguishability) through its body.
example (S : FixedLengthPKScheme) (atk : Attack) (h : S.NMSecure atk) (A : NUPPT) (q ℓ : PolyExpr)
    (D : NUPPT) : ∃ ε : ℕ → ℝ, Negligible ε ∧ ∀ n, advantage (S.nmGame atk A (q.eval n) (ℓ.eval n) D
      false n) (S.nmGame atk A (q.eval n) (ℓ.eval n) D true n) ≤ ε n := h A q ℓ D
-- 3. `OracleComp.AllOutputs` (Games) through its body.
example {α : Type} (P : α → Prop) (a : α) (h : (OracleComp.pure (spec := unifSpec) a).AllOutputs P) :
    P a := h
-- 4. `NUPPT.ofPolyTime` (Randomized) through its body.
example {f : List Bool → List Bool} (hf : PolyTimeComputable f) (c a : PolyExpr)
    (α : ℕ → List Bool) (hα : ∀ n, (α n).length ≤ a.eval n) :
    (NUPPT.ofPolyTime hf c a α hα).coins = c := rfl
-- 5. the helper `NMSim.snmDin` (Hybrid) through its body.
example (S : FixedLengthPKScheme) (pl : PolyExpr) : snmDin S pl 0 = S.ctLen := rfl
-- 6. the helper `NMSim.entryL` (Hybrid) through its body.
example (S : FixedLengthPKScheme) (n : ℕ) (sk c : List Bool) :
    entryL S n sk true c = true :: List.replicate (S.msgLen.eval n + 1) false := rfl
-- 7. the helper `NMSim.halfSamp` (SimIND) through its body.
example (S : FixedLengthPKScheme) : (halfSamp S).coins = .const 1 := rfl
-- 8. the helper `NMSim.simHandler` (SimINDGap) through its body.
example (S : FixedLengthPKScheme) (ℓ : PolyExpr) :
    simHandler S ℓ = copyHandler S (S.msgLen.add S.msgLen) (.const 0)
      ((ℓ.mul S.ctLen).add (.const 0)) := rfl
-- 9. the helper `NMSim.rdState` (Rounds) through its body.
example (w : List Bool) : rdState w = pairFstD (pairSndD w) := rfl
-- 10. the helper `NMSim.chalHandler` (Challenge) through its body.
example (S : FixedLengthPKScheme) (pl hl : PolyExpr) (P : ChalParams S pl hl 1 (fun _ => pl)
    (fun _ => hl)) : (chalHandler P).perCall = .const 1 := rfl
-- 11. the helper `NMSim.finSt` (Simulator) through its body.
example (w : List Bool) : finSt w = pairFstD (pairSndD w) := rfl
-- 12. the helper `NMSim.nmLen` (Reduction) through its body.
example (S : FixedLengthPKScheme) (pl r sl : PolyExpr) : nmLen S pl r sl =
    ((PolyExpr.const 3).mul r).add ((PolyExpr.const 2).mul ((pl.add S.msgLen).add sl)) := rfl
-- 13. the helper `NMSim.bitG` (Recover) through its body.
example (ctx ch : List Bool) : bitG ctx ch = [NMCCA2.guessBit ch] := rfl
-- 14. the owned file's `snmCodec` through its body.
example (S : FixedLengthPKScheme) (M : MsgSampler) (n r sl : ℕ) :
    S.snmCodec M n r sl = bitCodec (S.snmInLens M n) (S.snmOutLens M n) (r * S.ctLen.eval n + sl) :=
  rfl
