/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Encryption.PrivateKey.EncryptThenTag.Games
import TCSlib.Cryptography.Games.Efficiency
import TCSlib.Cryptography.Asymptotic.EnsemblesLemmas
import TCSlib.Cryptography.Asymptotic.CollectionsHelpers
import TCSlib.Cryptography.Asymptotic.OneWayLemmas
import TCSlib.Cryptography.Pseudorandom.Functions.Asymptotic.GGM.Reduction

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The handler of the tag-key PRF reduction

Step 1 of [PS10, Theorem 170.4] replaces the tag function `f_{k₂}` by a random function: a
reduction with oracle access to a function `g` on `2n` bits samples `k₁` itself, runs the CCA2
adversary and answers its queries with `g` in place of `f_{k₂}`. This file builds that reduction as a
`Games.InteractiveHandler` (`dHandler`) with one outer oracle (the function), so that T2
(`Games.exists_interactiveHandlerMachine`) and T4 (`Games.exists_toOracleAdversary_of_bitCodec`)
make it a next-query machine.

The handler's seed is the key `k₁` followed by `q(n)` nonce tapes of `n` bits (`dSeed`); its state
counts the queries and records the challenge (`dState`). The mask `c₁ = m ⊕ f_{k₁}(r)` is computed
with the evaluator `E`.
- `Enc` on `m`: with the next tape `r`, ask `g` at `r ‖ c₁` and answer `⟨r, ⟨c₁, g(r ‖ c₁)⟩⟩`.
- `Dec` on `w`: refuse the recorded challenge; if `w = ⟨r, ⟨c₁, t⟩⟩` has `n`-bit `r` and `c₁`, ask
  `g` at `r ‖ c₁` and answer `⟨1, c₁ ⊕ f_{k₁}(r)⟩` if the answer is `t`; otherwise answer `⊥`.
- `Challenge` on `⟨m₀, m₁⟩`: the first time, encrypt `m_b` as `Enc` does and record it; later
  repeat the record.
Every query advances the counter. The finalization asks nothing and outputs the adversary's bit.

## Main definitions

* `ETTGame.ettCt`, `ettDin`, `ettDout`, `tagLen`, `tagOut`, `dStLen`, `dSeedLen`: the lengths.
* `ETTGame.recBits`, `dState`, `dSeed`: the encoded state and seed.
* `ETTGame.dHandler E hE q b`: the handler.

## Main results

* `ETTGame.dHandler_impl_enc`, `_impl_dec_ref`, `_impl_dec_wf`, `_impl_dec_nwf`,
  `_impl_challenge_some`, `_impl_challenge_none`: its answers on encoded states.
* `ETTGame.dHandler_finish`, `dHandler_init_hstate`: the finalization and the initial state.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  Algorithm 169.3 and Theorem 170.4 (book pp. 169–171).
-/

namespace TCSlib.Cryptography.Composability.ETTGame

open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games
open TCSlib.Cryptography.Games.InteractiveHandler (rU rW rS rI rX rL rCnt rAns)

/-! ### Lengths -/

/-- The ciphertext length `6n + 4`. -/
def ettCt : PolyExpr := .add (.mul (.const 6) .var) (.const 4)

/-- `ettCt.eval n = 6n + 4`. -/
theorem ettCt_eval (n : ℕ) : ettCt.eval n = 6 * n + 4 := by
  rw [ettCt, PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const, PolyExpr.eval_const,
    PolyExpr.eval_var]

/-- The query lengths: `n`-bit messages to `Enc`, `(6n + 4)`-bit ciphertexts to `Dec`, `2n`-bit
challenge queries. -/
def ettDin : Fin 3 → PolyExpr
  | 0 => .var
  | 1 => ettCt
  | 2 => .add .var .var

/-- `ettDin 0 = var`. -/
theorem ettDin_zero : ettDin 0 = .var := rfl

/-- `ettDin 1 = ettCt`. -/
theorem ettDin_one : ettDin 1 = ettCt := rfl

/-- `ettDin 2 = var + var`. -/
theorem ettDin_two : ettDin 2 = .add .var .var := rfl

/-- The answer lengths: ciphertexts, `(n + 1)`-bit decryption answers, ciphertexts. -/
def ettDout : Fin 3 → PolyExpr
  | 0 => ettCt
  | 1 => .add .var (.const 1)
  | 2 => ettCt

/-- `ettDout 0 = ettCt`. -/
theorem ettDout_zero : ettDout 0 = ettCt := rfl

/-- `ettDout 1 = var + 1`. -/
theorem ettDout_one : ettDout 1 = .add .var (.const 1) := rfl

/-- `ettDout 2 = ettCt`. -/
theorem ettDout_two : ettDout 2 = ettCt := rfl

/-- The tag length `2n`. -/
def tagLen : PolyExpr := .mul (.const 2) .var

/-- `tagLen.eval n = 2n`. -/
theorem tagLen_eval (n : ℕ) : tagLen.eval n = 2 * n := by
  rw [tagLen, PolyExpr.eval_mul, PolyExpr.eval_const, PolyExpr.eval_var]

/-- The outer oracle: `2n`-bit queries and answers. -/
abbrev tagOut : Fin 1 → PolyExpr := fun _ => tagLen

/-- `tagOut j = tagLen`. -/
theorem tagOut_eq (j : Fin 1) : tagOut j = tagLen := rfl

variable (q : PolyExpr)

/-- The state length `2q + 3 + (6n + 4)`. -/
def dStLen : PolyExpr := .add (.add (.mul (.const 2) q) (.const 3)) ettCt

/-- `dStLen q = 2q + 3 + ettCt`. -/
theorem dStLen_eq : dStLen q = .add (.add (.mul (.const 2) q) (.const 3)) ettCt := rfl

/-- The seed length `n + q(n) · n`: the key and the tapes. -/
def dSeedLen : PolyExpr := .add .var (.mul q .var)

/-- `(dSeedLen q).eval n = n + q(n) · n`. -/
theorem dSeedLen_eval (n : ℕ) : (dSeedLen q).eval n = n + q.eval n * n := by
  rw [dSeedLen, PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_var]

/-- The record of the challenge: `1 :: c` once recorded, `0^{1 + ct(n)}` before. -/
def recBits (n : ℕ) : Option (Fin (ettCt.eval n) → Bool) → List Bool
  | none => false :: List.replicate (ettCt.eval n) false
  | some c => true :: List.ofFn c

/-- `recBits n none = 0^{1 + ct(n)}`. -/
theorem recBits_none (n : ℕ) : recBits n none = false :: List.replicate (ettCt.eval n) false :=
  rfl

/-- `recBits n (some c) = 1 :: ⟦c⟧`. -/
theorem recBits_some (n : ℕ) (c : Fin (ettCt.eval n) → Bool) :
    recBits n (some c) = true :: List.ofFn c := rfl

/-- The record has `1 + ct(n)` bits. -/
theorem length_recBits (n : ℕ) (o : Option (Fin (ettCt.eval n) → Bool)) :
    (recBits n o).length = ettCt.eval n + 1 := by
  cases o with
  | none => rw [recBits_none, List.length_cons, List.length_replicate]
  | some c => rw [recBits_some, List.length_cons, List.length_ofFn]

/-- **The encoded state** after `j` queries, with the challenge record `o`:
`⟨1^j, recBits o⟩`, padded with `false` to the state length. -/
def dState (n j : ℕ) (o : Option (Fin (ettCt.eval n) → Bool)) :
    Fin ((dStLen q).eval n) → Bool :=
  padFin _ (pairEncode (List.replicate j true) (recBits n o))

/-- `dState q n j o = padFin _ ⟨1^j, recBits n o⟩`. -/
theorem dState_eq (n j : ℕ) (o : Option (Fin (ettCt.eval n) → Bool)) :
    dState q n j o = padFin _ (pairEncode (List.replicate j true) (recBits n o)) := rfl

/-- **The seed** from the key `k₁` and the tape word: `⟦dSeed q n (k, W)⟧ = ⟦k⟧ ++ ⟦W⟧`. -/
def dSeed (n : ℕ) :
    (Fin n → Bool) × (Fin (q.eval n * n) → Bool) ≃ (Fin ((dSeedLen q).eval n) → Bool) :=
  EnsembleLemmas.coinsEquiv (dSeedLen_eval q n)

/-- `dSeed q n = coinsEquiv (dSeedLen_eval q n)`. -/
theorem dSeed_eq (n : ℕ) : dSeed q n = EnsembleLemmas.coinsEquiv (dSeedLen_eval q n) := rfl

/-- `⟦dSeed q n (k, W)⟧ = ⟦k⟧ ++ ⟦W⟧`. -/
theorem ofFn_dSeed (n : ℕ) (kW : (Fin n → Bool) × (Fin (q.eval n * n) → Bool)) :
    List.ofFn (dSeed q n kW) = List.ofFn kW.1 ++ List.ofFn kW.2 :=
  EnsembleLemmas.ofFn_coinsEquiv _ _

/-- The tape `j` of the tape word: block `j` of `W` (`EnsembleLemmas.blocks`). -/
def dTape (n : ℕ) (W : Fin (q.eval n * n) → Bool) (j : ℕ) (hj : j < q.eval n) : Fin n → Bool :=
  EnsembleLemmas.blocks (q.eval n) n W ⟨j, hj⟩

/-- `dTape q n W j hj = blocks (q n) n W ⟨j, hj⟩`. -/
theorem dTape_eq (n : ℕ) (W : Fin (q.eval n * n) → Bool) (j : ℕ) (hj : j < q.eval n) :
    dTape q n W j hj = EnsembleLemmas.blocks (q.eval n) n W ⟨j, hj⟩ := rfl

/-! ### Strings -/

/-- The fields of an encoded state with `j ≤ q(n)`: the count `1^j`, the flag and the record. -/
private theorem fields_dState (n j : ℕ) (o : Option (Fin (ettCt.eval n) → Bool))
    (hj : j ≤ q.eval n) :
    pairFstD (List.ofFn (dState q n j o)) = List.replicate j true ∧
      (pairSndD (List.ofFn (dState q n j o))).headD false = o.isSome ∧
      ((pairSndD (List.ofFn (dState q n j o))).drop 1).take (ettCt.eval n) =
        (recBits n o).drop 1 := by
  have hlen : (pairEncode (List.replicate j true) (recBits n o)).length ≤ (dStLen q).eval n := by
    rw [length_pairEncode, List.length_replicate, length_recBits, dStLen_eq, PolyExpr.eval_add,
      PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const, PolyExpr.eval_const]
    omega
  rw [dState_eq, Collection.ofFn_padFin_of_le hlen, ← GGMRed.pairEncode_append_right]
  rw [pairFstD_pairEncode, pairSndD_pairEncode]
  refine ⟨rfl, ?_, ?_⟩
  · cases o <;> rfl
  · cases o with
    | none =>
      rw [recBits_none, List.cons_append, List.drop_succ_cons, List.drop_zero, List.drop_succ_cons,
        List.drop_zero, List.take_left' List.length_replicate]
    | some c =>
      rw [recBits_some, List.cons_append, List.drop_succ_cons, List.drop_zero, List.drop_succ_cons,
        List.drop_zero, List.take_left' List.length_ofFn]

/-! ### The round function -/

/-- The challenge flag of the state. -/
private def rFlag (w : List Bool) : Bool := (pairSndD (rS w)).headD false
/-- The recorded challenge of the state. -/
private def rRec (w : List Bool) : List Bool :=
  ((pairSndD (rS w)).drop 1).take (ettCt.eval (rU w).length)
/-- The key `k₁` of the seed. -/
private def rKey (w : List Bool) : List Bool := (rW w).take (rU w).length
/-- Tape `j` of the seed, `j` the query count. -/
private def rNonce (w : List Bool) : List Bool :=
  ((rW w).drop ((rU w).length + (rCnt w).length * (rU w).length)).take (rU w).length
/-- The mask `m ⊕ E⟨k₁, r⟩` with the tape `r`. -/
private def rMask (E : List Bool → List Bool) (w m : List Bool) : List Bool :=
  List.zipWith xor m (E (pairEncode (rKey w) (rNonce w)))
/-- The ciphertext `⟨r, ⟨c₁, y⟩⟩` with the tape `r` and the outer answer `y`. -/
private def rCt (E : List Bool → List Bool) (w m : List Bool) : List Bool :=
  pairEncode (rNonce w) (pairEncode (rMask E w m) (rAns w))
/-- The selected challenge message `m_b`. -/
private def rMsg (b : Bool) (w : List Bool) : List Bool :=
  if b then (rX w).drop (rU w).length else (rX w).take (rU w).length
/-- Whether the decryption query `⟨r, ⟨c₁, t⟩⟩` has `n`-bit `r` and `c₁`. -/
private def rWF (w : List Bool) : Bool :=
  decide ((pairFstD (rX w)).length = (rU w).length) &&
    decide ((pairFstD (pairSndD (rX w))).length = (rU w).length)
/-- Whether the decryption query is the recorded challenge. -/
private def rRef (w : List Bool) : Bool := rFlag w && decide (rX w = rRec w)
/-- The decryption `⟨1, c₁ ⊕ E⟨k₁, r⟩⟩` of the query. -/
private def rDec (E : List Bool → List Bool) (w : List Bool) : List Bool :=
  true :: List.zipWith xor (pairFstD (pairSndD (rX w))) (E (pairEncode (rKey w) (pairFstD (rX w))))
/-- Whether the outer answer is the tag of the query. -/
private def rOK (w : List Bool) : Bool := decide (rAns w = pairSndD (pairSndD (rX w)))
/-- The all-`false` decryption answer `⊥`. -/
private def rZero (w : List Bool) : List Bool :=
  List.replicate ((PolyExpr.add .var (.const 1)).eval (rU w).length) false
/-- The new state after a query: count `j + 1`, record `t`. -/
private def rNew (w t : List Bool) : List Bool :=
  EnsembleLemmas.padL ((dStLen q).eval (rU w).length) (pairEncode (true :: rCnt w) t)

/-- **One round of the handler** (see the module docstring), for the challenge bit `b`. A first
round of `Enc`, of a first challenge or of a well-formed decryption asks the outer oracle; the second
round, with the answer `y` in the log, returns the answer and the new state. -/
private def dRun (E : List Bool → List Bool) (b : Bool) (w : List Bool) : List Bool :=
  if (rI w).headD false then
    if ((rI w).drop 1).headD false then
      if rFlag w then pairEncode [true] (rRec w ++ rNew q w (true :: rRec w))
      else if decide (rL w = []) then
        pairEncode [false] (pairEncode [] (rNonce w ++ rMask E w (rMsg b w)))
      else pairEncode [true] (rCt E w (rMsg b w) ++ rNew q w (true :: rCt E w (rMsg b w)))
    else
      if rRef w then pairEncode [true] (rZero w ++ rNew q w (rFlag w :: rRec w))
      else if rWF w then
        if decide (rL w = []) then
          pairEncode [false] (pairEncode [] (pairFstD (rX w) ++ pairFstD (pairSndD (rX w))))
        else pairEncode [true]
          ((if rOK w then rDec E w else rZero w) ++ rNew q w (rFlag w :: rRec w))
      else pairEncode [true] (rZero w ++ rNew q w (rFlag w :: rRec w))
  else
    if decide (rL w = []) then pairEncode [false] (pairEncode [] (rNonce w ++ rMask E w (rX w)))
    else pairEncode [true] (rCt E w (rX w) ++ rNew q w (rFlag w :: rRec w))

/-- The round function is polynomial-time.

**Proof sketch.** Pair projections; the key and the tape by `pairTakePoly`, `unaryMulPair` and
`dropPrefixByLength`; the mask and the decryption by the evaluator `E` and `pairXor`; the tests
by `lenEq_poly` and `pairEq`; the padded new state by `padL`; and `polyTimeComputable_ite` for
the cases. -/
private theorem polyTimeComputable_dRun {E : List Bool → List Bool} (hE : PolyTimeComputable E)
    (b : Bool) : PolyTimeComputable (dRun q E b) := by
  have hF := polyTimeComputable_pairFstD
  have hD := polyTimeComputable_pairSndD
  have hU : PolyTimeComputable rU := InteractiveHandler.polyTimeComputable_rU
  have hW : PolyTimeComputable rW := InteractiveHandler.polyTimeComputable_rW
  have hS : PolyTimeComputable rS := InteractiveHandler.polyTimeComputable_rS
  have hI : PolyTimeComputable rI := InteractiveHandler.polyTimeComputable_rI
  have hX : PolyTimeComputable rX := InteractiveHandler.polyTimeComputable_rX
  have hL : PolyTimeComputable rL := InteractiveHandler.polyTimeComputable_rL
  have hCnt : PolyTimeComputable rCnt := InteractiveHandler.polyTimeComputable_rCnt
  have hY : PolyTimeComputable rAns := InteractiveHandler.polyTimeComputable_rAns
  have hT : PolyTimeComputable fun w => pairSndD (rS w) := hD.comp hS
  have hFlag : PolyTimeComputable fun w => [rFlag w] := polyTimeComputable_headD.comp hT
  have hRec : PolyTimeComputable rRec :=
    ((polyTimeComputable_pairTakePoly ettCt).comp
      (hU.pairEncode (polyTimeComputable_tail.comp hT))).congr fun w => by
        simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]; rfl
  have hKey : PolyTimeComputable rKey :=
    ((polyTimeComputable_pairTakePoly .var).comp (hU.pairEncode hW)).congr fun w => by
      simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode,
        PolyExpr.eval_var]; rfl
  have hU1 : PolyTimeComputable fun w => List.replicate (rU w).length true :=
    ((polyTimeComputable_unaryPoly .var).comp hU).congr fun w => by
      simp only [Function.comp_apply, PolyExpr.eval_var]
  have hOff : PolyTimeComputable fun w =>
      List.replicate ((rU w).length + (rCnt w).length * (rU w).length) true :=
    (hU1.append (OneWay.polyTimeComputable_unaryMulPair.comp (hCnt.pairEncode hU))).congr
      fun w => by
        simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode,
          List.replicate_add]
  have hDrop : PolyTimeComputable fun w =>
      (rW w).drop ((rU w).length + (rCnt w).length * (rU w).length) :=
    (polyTimeComputable_dropPrefixByLength.comp (hOff.pairEncode hW)).congr fun w => by
      simp only [Function.comp_apply, PrefixByLength.drop_def, pairFstD_pairEncode,
        pairSndD_pairEncode, List.length_replicate]
  have hNonce : PolyTimeComputable rNonce :=
    ((polyTimeComputable_pairTakePoly .var).comp (hU.pairEncode hDrop)).congr fun w => by
      simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode,
        PolyExpr.eval_var]; rfl
  have hXor : ∀ {m p : List Bool → List Bool}, PolyTimeComputable m → PolyTimeComputable p →
      PolyTimeComputable fun w => List.zipWith xor (m w) (p w) := fun hm hp =>
    (polyTimeComputable_pairXor.comp (hm.pairEncode hp)).congr fun w => by
      simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]
  have hMask : ∀ {m : List Bool → List Bool}, PolyTimeComputable m →
      PolyTimeComputable fun w => rMask E w (m w) := fun hm =>
    hXor hm (hE.comp (hKey.pairEncode hNonce))
  have hCt : ∀ {m : List Bool → List Bool}, PolyTimeComputable m →
      PolyTimeComputable fun w => rCt E w (m w) := fun hm =>
    hNonce.pairEncode ((hMask hm).pairEncode hY)
  have hMsg : PolyTimeComputable (rMsg b) :=
    polyTimeComputable_ite (polyTimeComputable_const [b])
      (((polyTimeComputable_pairDropPoly .var).comp (hU.pairEncode hX)).congr fun w => by
        simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode,
          PolyExpr.eval_var])
      (((polyTimeComputable_pairTakePoly .var).comp (hU.pairEncode hX)).congr fun w => by
        simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode,
          PolyExpr.eval_var])
  have hR : PolyTimeComputable fun w => pairFstD (rX w) := hF.comp hX
  have hC : PolyTimeComputable fun w => pairFstD (pairSndD (rX w)) := (hF.comp hD).comp hX
  have hTg : PolyTimeComputable fun w => pairSndD (pairSndD (rX w)) := (hD.comp hD).comp hX
  have hWF : PolyTimeComputable fun w => [rWF w] :=
    polyTimeComputable_and (EffFill.lenEq_poly hR hU) (EffFill.lenEq_poly hC hU)
  have hEq : ∀ {u v : List Bool → List Bool}, PolyTimeComputable u → PolyTimeComputable v →
      PolyTimeComputable fun w => [decide (u w = v w)] := fun hu hv =>
    (polyTimeComputable_pairEq.comp (hu.pairEncode hv)).congr fun w => by
      simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]
  have hRef : PolyTimeComputable fun w => [rRef w] := polyTimeComputable_and hFlag (hEq hX hRec)
  have hOK : PolyTimeComputable fun w => [rOK w] := hEq hY hTg
  have hDec : PolyTimeComputable (rDec E) :=
    (polyTimeComputable_const [true]).append (hXor hC (hE.comp (hKey.pairEncode hR)))
  have hZero : PolyTimeComputable rZero := EnsembleLemmas.polyTimeComputable_zeros _ hU
  have hNew : ∀ {t : List Bool → List Bool}, PolyTimeComputable t →
      PolyTimeComputable fun w => rNew q w (t w) := fun ht =>
    EnsembleLemmas.polyTimeComputable_padL (dStLen q) hU
      (((polyTimeComputable_const [true]).append hCnt).pairEncode ht)
  have hRet : ∀ {f : List Bool → List Bool}, PolyTimeComputable f →
      PolyTimeComputable fun w => pairEncode [true] (f w) := fun hf =>
    (polyTimeComputable_const [true]).pairEncode hf
  have hQry : ∀ {f : List Bool → List Bool}, PolyTimeComputable f →
      PolyTimeComputable fun w => pairEncode [false] (pairEncode [] (f w)) := fun hf =>
    (polyTimeComputable_const [false]).pairEncode ((polyTimeComputable_const []).pairEncode hf)
  have cNil : PolyTimeComputable fun w => [decide (rL w = [])] := polyTimeComputable_isNil.comp hL
  have hKeep : PolyTimeComputable fun w => rFlag w :: rRec w :=
    (hFlag.append hRec).congr fun _ => rfl
  have hTrueRec : PolyTimeComputable fun w => true :: rRec w :=
    (polyTimeComputable_const [true]).append hRec
  have hChal := polyTimeComputable_ite hFlag (hRet (hRec.append (hNew hTrueRec)))
    (polyTimeComputable_ite cNil (hQry (hNonce.append (hMask hMsg)))
      (hRet ((hCt hMsg).append (hNew ((polyTimeComputable_const [true]).append (hCt hMsg))))))
  have hDecR := polyTimeComputable_ite hRef (hRet (hZero.append (hNew hKeep)))
    (polyTimeComputable_ite hWF
      (polyTimeComputable_ite cNil (hQry (hR.append hC))
        (hRet ((polyTimeComputable_ite hOK hDec hZero).append (hNew hKeep))))
      (hRet (hZero.append (hNew hKeep))))
  have hEnc := polyTimeComputable_ite cNil (hQry (hNonce.append (hMask hX)))
    (hRet ((hCt hX).append (hNew hKeep)))
  exact polyTimeComputable_ite (polyTimeComputable_headD.comp hI)
    (polyTimeComputable_ite (polyTimeComputable_headD.comp (polyTimeComputable_tail.comp hI))
      hChal hDecR) hEnc

/-- The finalization's round: output `A`'s bit, `⟨[true], a⟩` on `⟨ctx, ⟨s, ⟨a, L⟩⟩⟩`. -/
private def dFin (w : List Bool) : List Bool :=
  pairEncode [true] (pairFstD (pairSndD (pairSndD w)))

/-- The finalization's round is polynomial-time. -/
private theorem polyTimeComputable_dFin : PolyTimeComputable dFin :=
  (polyTimeComputable_const [true]).pairEncode
    (polyTimeComputable_pairFstD.comp
      (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD))

/-! ### The handler -/

/-- **The handler of the tag-key PRF reduction** for the evaluator `E`, the budget `q` and the
challenge bit `b`: state `dState j o` (initially `j = 0` and no record), seed `dSeed` (the key and
`q(n)` tapes), one outer call per inner query, the adversary run on the empty input, and the
finalization outputting the adversary's bit. -/
noncomputable def dHandler (E : List Bool → List Bool) (hE : PolyTimeComputable E) (b : Bool) :
    InteractiveHandler 3 ettDin ettDout 1 tagOut tagOut where
  stateLen := dStLen q
  seedLen := dSeedLen q
  perCall := .const 1
  init n := dState q n 0 none
  run := dRun q E b
  poly := polyTimeComputable_dRun q hE b
  advIn _ := []
  advIn_poly := polyTimeComputable_const []
  outLen := .const 1
  finCall := .const 0
  finRun := dFin
  finRun_poly := polyTimeComputable_dFin

attribute [simps (config := { isSimp := false }) stateLen seedLen perCall outLen finCall]
  dHandler

variable (E : List Bool → List Bool) (hE : PolyTimeComputable E) (b : Bool)

/-- The encoded state at the handler's state type: `dHState … n j o = dState q n j o`. -/
def dHState (n j : ℕ) (o : Option (Fin (ettCt.eval n) → Bool)) :
    Fin ((dHandler q E hE b).stateLen.eval n) → Bool :=
  dState q n j o

/-- `dHState q E hE b n j o = dState q n j o`. -/
theorem dHState_eq (n j : ℕ) (o : Option (Fin (ettCt.eval n) → Bool)) :
    dHState q E hE b n j o = dState q n j o := rfl

/-- The seed at the handler's seed type: `dHSeed … n = dSeed q n`. -/
def dHSeed (n : ℕ) :
    (Fin n → Bool) × (Fin (q.eval n * n) → Bool) ≃ (Fin ((dHandler q E hE b).seedLen.eval n) → Bool) :=
  dSeed q n

/-- `dHSeed q E hE b n = dSeed q n`. -/
theorem dHSeed_eq (n : ℕ) : dHSeed q E hE b n = dSeed q n := rfl

/-- The initial state is the encoded `(0, none)`. -/
theorem dHandler_init_hstate (n : ℕ) : (dHandler q E hE b).init n = dHState q E hE b n 0 none :=
  rfl

/-- The adversary's input is empty: `(dHandler q E hE b).advInput n z ω = []`. -/
theorem dHandler_advInput (n : ℕ) (z : List Bool)
    (ω : Fin ((dHandler q E hE b).seedLen.eval n) → Bool) :
    (dHandler q E hE b).advInput n z ω = [] := rfl

/-- The finalization outputs the adversary's bit and asks nothing:
`(dHandler q E hE b).finish n z ω s a = pure (padFin _ ⟦a⟧)`. -/
theorem dHandler_finish (n : ℕ) (z : List Bool)
    (ω : Fin ((dHandler q E hE b).seedLen.eval n) → Bool)
    (s : Fin ((dHandler q E hE b).stateLen.eval n) → Bool)
    (a : Fin ((PolyExpr.const 1).eval n) → Bool) :
    (dHandler q E hE b).finish n z ω s a =
      .pure (padFin ((dHandler q E hE b).outLen.eval n) (List.ofFn a)) := by
  rw [InteractiveHandler.finish_eq]
  have h0 : (dHandler q E hE b).finCall.eval n = 0 := by
    rw [dHandler_finCall, PolyExpr.eval_const]
  rw [h0]
  refine buildComp_zero_of_ret ?_
  show decodeBitMove _ _ _ (dFin _) = _
  rw [dFin, InteractiveHandler.finInput_eq, pairSndD_pairEncode, pairSndD_pairEncode,
    pairFstD_pairEncode]
  have hw : List.ofFn (padFin ((dHandler q E hE b).outLen.eval n) (List.ofFn a)) =
      List.ofFn a :=
    ofFn_padFin_of_length (by rw [List.length_ofFn, dHandler_outLen])
  exact (congrArg (fun w => decodeBitMove _ _ _ (pairEncode [true] w)) hw).symm.trans
    (decodeBitMove_ret _ _ _ _)

/-! ### Answers of the handler -/

/-- `⟦dHSeed … n (k, W)⟧ = ⟦k⟧ ++ ⟦W⟧`. -/
theorem ofFn_dHSeed (n : ℕ) (kW : (Fin n → Bool) × (Fin (q.eval n * n) → Bool)) :
    List.ofFn (dHSeed q E hE b n kW) = List.ofFn kW.1 ++ List.ofFn kW.2 :=
  ofFn_dSeed q n kW

/-- `⟦dHState … n j o⟧ = ⟦dState q n j o⟧`. -/
theorem ofFn_dHState (n j : ℕ) (o : Option (Fin (ettCt.eval n) → Bool)) :
    List.ofFn (dHState q E hE b n j o) = List.ofFn (dState q n j o) :=
  rfl

section Answers

variable (F : ∀ n, (Fin n → Bool) → (Fin n → Bool) → (Fin n → Bool))
  (hFE : ∀ n (s x : Fin n → Bool), E (pairEncode (List.ofFn s) (List.ofFn x)) =
    List.ofFn (F n s x))
  (n : ℕ) (z : List Bool) (k : Fin n → Bool) (W : Fin (q.eval n * n) → Bool)

/-- The round input of a call, field by field, on an encoded state with `j < q(n)` and the seed
`dHSeed (k, W)`. -/
private theorem fields_input {i : Fin 3} (x L : List Bool) (j : ℕ)
    (o : Option (Fin (ettCt.eval n) → Bool)) (hj : j < q.eval n) :
    let w := InteractiveHandler.input n z (List.ofFn (dHSeed q E hE b n (k, W)))
      (List.ofFn (dHState q E hE b n j o)) i x L
    rU w = List.replicate n true ∧ rS w = List.ofFn (dHState q E hE b n j o) ∧
      rI w = List.replicate i true ∧ rX w = x ∧ rL w = L ∧ rCnt w = List.replicate j true ∧
      rFlag w = o.isSome ∧ rRec w = (recBits n o).drop 1 ∧ rKey w = List.ofFn k ∧
      rNonce w = List.ofFn (dTape q n W j hj) := by
  obtain ⟨h₁, h₂, h₃⟩ := fields_dState q n j o hj.le
  have hW : rW (InteractiveHandler.input n z (List.ofFn (dHSeed q E hE b n (k, W)))
      (List.ofFn (dHState q E hE b n j o)) i x L) = List.ofFn k ++ List.ofFn W := by
    rw [InteractiveHandler.rW_input, ofFn_dHSeed]
  have hS : rS (InteractiveHandler.input n z (List.ofFn (dHSeed q E hE b n (k, W)))
      (List.ofFn (dHState q E hE b n j o)) i x L) = List.ofFn (dState q n j o) :=
    (InteractiveHandler.rS_input ..).trans (ofFn_dHState q E hE b n j o)
  have hcnt : rCnt (InteractiveHandler.input n z (List.ofFn (dHSeed q E hE b n (k, W)))
      (List.ofFn (dHState q E hE b n j o)) i x L) = List.replicate j true := by
    rw [rCnt, hS, h₁]
  have hU := InteractiveHandler.rU_input (k := 3) n z (List.ofFn (dHSeed q E hE b n (k, W)))
    (List.ofFn (dHState q E hE b n j o)) i x L
  refine ⟨hU, InteractiveHandler.rS_input .., InteractiveHandler.rI_input ..,
    InteractiveHandler.rX_input .., InteractiveHandler.rL_input .., hcnt, ?_, ?_, ?_, ?_⟩
  · rw [rFlag, hS, h₂]
  · rw [rRec, hS, hU, List.length_replicate, h₃]
  · rw [rKey, hW, hU, List.length_replicate, List.take_left' List.length_ofFn]
  · rw [rNonce, hW, hU, hcnt, List.length_replicate, List.length_replicate, List.drop_append,
      List.drop_eq_nil_of_le (by rw [List.length_ofFn]; omega), List.nil_append, List.length_ofFn,
      Nat.add_sub_cancel_left, dTape_eq]
    exact EnsembleLemmas.take_drop_ofFn_blocks W j hj

/-- The new state after a query from `dState j o`, with record `t`. -/
private theorem rNew_fields {i : Fin 3} (x L : List Bool) (j : ℕ)
    (o o' : Option (Fin (ettCt.eval n) → Bool)) (hj : j < q.eval n) :
    rNew q (InteractiveHandler.input n z (List.ofFn (dHSeed q E hE b n (k, W)))
        (List.ofFn (dHState q E hE b n j o)) i x L) (recBits n o') =
      List.ofFn (dHState q E hE b n (j + 1) o') := by
  obtain ⟨hU, -, -, -, -, hCnt, -, -, -, -⟩ := fields_input q E hE b n z k W (i := i) x L j o hj
  rw [rNew, hU, hCnt, List.length_replicate, ofFn_dHState, dState_eq,
    EnsembleLemmas.ofFn_padFin_eq_padL, List.replicate_succ]

/-- The flag and the record rebuild the record bits: `rFlag :: rRec = recBits o`. -/
private theorem recBits_fields (o : Option (Fin (ettCt.eval n) → Bool)) :
    o.isSome :: (recBits n o).drop 1 = recBits n o := by
  cases o <;> rfl

/-- The outer answer recorded in a one-entry log. -/
private theorem rY_one (w : List Bool) (x' y : List Bool)
    (hL : rL w = pairEncode (pairEncode [] (pairEncode x' y)) []) : rAns w = y := by
  rw [InteractiveHandler.rAns_eq, hL, pairFstD_pairEncode, pairSndD_pairEncode,
    pairSndD_pairEncode]

/-- A one-entry log is not empty. -/
private theorem log_ne_nil (x' y : List Bool) :
    decide (pairEncode (pairEncode [] (pairEncode x' y)) [] = []) = false :=
  decide_eq_false (pairEncode_ne_nil _ _)

include hFE in
/-- The mask computed with the evaluator: `m ⊕ E⟨⟦k⟧, ⟦r⟧⟩ = maskL (F n k) r m`. -/
private theorem mask_eval (r : Fin n → Bool) (m : List Bool) :
    List.zipWith xor m (E (pairEncode (List.ofFn k) (List.ofFn r))) = maskL (F n k) r m := by
  rw [hFE, maskL_eq]

/-- The outer query word of a pair `r ‖ c₁` with `|r| = |c₁| = n`, read at `2n` bits. -/
private theorem ofFn_padFin_pair {r c : List Bool} (hr : r.length = n) (hc : c.length = n) :
    List.ofFn (padFin ((tagOut 0).eval n) (r ++ c)) = r ++ c :=
  ofFn_padFin_of_length (by rw [List.length_append, hr, hc, tagOut_eq, tagLen_eval]; omega)

/-- The all-`false` decryption answer as a list. -/
private theorem rZero_fields (w : List Bool) (hU : rU w = List.replicate n true) :
    rZero w = List.ofFn (padFin ((ettDout 1).eval n) ([] : List Bool)) := by
  rw [rZero, hU, List.length_replicate, padFin_nil, ofFn_zeroBits, ettDout_one]

/-- The ciphertext of a nonce and an `n`-bit mask with a `2n`-bit tag has `6n + 4` bits. -/
private theorem length_ctW_tag {r c t : List Bool} (hr : r.length = n) (hc : c.length = n)
    (ht : t.length = 2 * n) : (ctW r c t).length = ettCt.eval n := by
  rw [ctW_eq, length_pairEncode, length_pairEncode, hr, hc, ht, ettCt_eval]
  omega

include hFE in
/-- **Encryption with the next tape:** from `dState j o` with `j < q(n)`, the query `m` asks the
outer oracle at `r ‖ c₁` with the tape `r` and `c₁ = maskL f_k r m`; its answer `y` gives the
ciphertext `⟨r, ⟨c₁, y⟩⟩` and the state `dState (j + 1) o`.

**Proof sketch.** Read the round input field by field (`fields_input`); the first round, with an
empty log, asks `r ‖ c₁` (`mask_eval`); the second, with the answer `y` in the log (`rY_one`),
returns `⟨r, ⟨c₁, y⟩⟩` and the state with count `j + 1` (`rNew_fields`);
`InteractiveHandler.impl_of_query` assembles the two rounds. -/
theorem dHandler_impl_enc (x : Fin ((ettDin 0).eval n) → Bool) (j : ℕ)
    (o : Option (Fin (ettCt.eval n) → Bool)) (hj : j < q.eval n) :
    (dHandler q E hE b).impl n z (dHSeed q E hE b n (k, W)) 0 x (dHState q E hE b n j o) =
      .query 0 (padFin _ (List.ofFn (dTape q n W j hj) ++
          maskL (F n k) (dTape q n W j hj) (List.ofFn x))) fun y =>
        .pure (padFin _ (ctW (List.ofFn (dTape q n W j hj))
          (maskL (F n k) (dTape q n W j hj) (List.ofFn x)) (List.ofFn y)),
          dHState q E hE b n (j + 1) o) := by
  have hx : (List.ofFn x).length = n := by rw [List.length_ofFn, ettDin_zero, PolyExpr.eval_var]
  have hm := length_maskL (F n k) (dTape q n W j hj) hx
  refine InteractiveHandler.impl_of_query _ n z _ x _ 0 _ _ _
    (by rw [dHandler_perCall, PolyExpr.eval_const]) ?_ ?_
  · show dRun q E b _ = _
    obtain ⟨-, -, hI, hX, hL, -, -, -, hK, hN⟩ :=
      fields_input q E hE b n z k W (i := 0) (List.ofFn x) [] j o hj
    rw [dRun, hI, Fin.val_zero, List.replicate_zero, List.headD_nil, if_neg Bool.false_ne_true,
      hL, if_pos (decide_eq_true rfl), rMask, hK, hN, hX, mask_eval E F hFE n k,
      ofFn_padFin_pair n List.length_ofFn hm]
    rfl
  · intro y
    show dRun q E b _ = _
    simp only [Fin.val_zero, List.replicate_zero]
    obtain ⟨-, -, hI, hX, hL, -, hFlag, hRec, hK, hN⟩ :=
      fields_input q E hE b n z k W (i := 0) (List.ofFn x)
        (pairEncode (pairEncode [] (pairEncode (List.ofFn (padFin ((tagOut 0).eval n)
          (List.ofFn (dTape q n W j hj) ++ maskL (F n k) (dTape q n W j hj) (List.ofFn x))))
          (List.ofFn y))) []) j o hj
    have hY := rY_one _ _ _ hL
    have hct : List.ofFn (padFin ((ettDout 0).eval n) (ctW (List.ofFn (dTape q n W j hj))
        (maskL (F n k) (dTape q n W j hj) (List.ofFn x)) (List.ofFn y))) =
        ctW (List.ofFn (dTape q n W j hj)) (maskL (F n k) (dTape q n W j hj) (List.ofFn x))
          (List.ofFn y) :=
      ofFn_padFin_of_length (by
        rw [length_ctW_tag n List.length_ofFn hm (by rw [List.length_ofFn, tagOut_eq, tagLen_eval]),
          ettDout_zero])
    rw [dRun, hI, Fin.val_zero, List.replicate_zero, List.headD_nil, if_neg Bool.false_ne_true, hL,
      log_ne_nil,
      if_neg Bool.false_ne_true, hct, rCt, rMask, hK, hN, hX, hY, mask_eval E F hFE n k, hFlag,
      hRec, recBits_fields, rNew_fields q E hE b n z k W (i := 0) _ _ j o o hj, ctW_eq]

/-- **A refused decryption:** from `dState j o` with the query the recorded challenge, the answer
is `⊥` and the state is `dState (j + 1) o`. -/
theorem dHandler_impl_dec_ref (x : Fin ((ettDin 1).eval n) → Bool) (j : ℕ)
    (o : Option (Fin (ettCt.eval n) → Bool)) (hj : j < q.eval n)
    (href : refW o (List.ofFn x) = true) :
    (dHandler q E hE b).impl n z (dHSeed q E hE b n (k, W)) 1 x (dHState q E hE b n j o) =
      .pure (padFin _ [], dHState q E hE b n (j + 1) o) := by
  refine InteractiveHandler.impl_of_ret _ n z _ x _ _ _ ?_
  show dRun q E b _ = _
  obtain ⟨hU, -, hI, hX, -, -, hFlag, hRec, -, -⟩ :=
    fields_input q E hE b n z k W (i := 1) (List.ofFn x) [] j o hj
  have hRef : rRef (InteractiveHandler.input n z (List.ofFn (dHSeed q E hE b n (k, W)))
      (List.ofFn (dHState q E hE b n j o)) (1 : Fin 3) (List.ofFn x) []) = true := by
    rw [rRef, hFlag, hRec, hX]
    cases o with
    | none => rw [refW_none] at href; cases href
    | some c =>
      rw [refW_some, decide_eq_true_eq] at href
      rw [recBits_some, List.drop_succ_cons, List.drop_zero, href]
      simp
  rw [dRun, hI, Fin.val_one, List.replicate_one, List.headD_cons, if_pos rfl, List.drop_succ_cons,
    List.drop_zero, List.headD_nil, if_neg Bool.false_ne_true, hRef, if_pos rfl,
    rZero_fields n _ hU, hFlag, hRec, recBits_fields,
    rNew_fields q E hE b n z k W (i := 1) _ _ j o o hj]

include hFE in
/-- **A well-formed decryption:** from `dState j o` with a query `w = ⟦x⟧` that is not refused and
has `n`-bit `wR w` and `wC w`, the query asks the outer oracle at `wR w ‖ wC w`; its answer `y`
gives `decL f_k w` if `⟦y⟧ = wT w` and `⊥` otherwise; the state is `dState (j + 1) o`. -/
theorem dHandler_impl_dec_wf (x : Fin ((ettDin 1).eval n) → Bool) (j : ℕ)
    (o : Option (Fin (ettCt.eval n) → Bool)) (hj : j < q.eval n)
    (href : refW o (List.ofFn x) = false) (hwf : wfW n (List.ofFn x) = true) :
    (dHandler q E hE b).impl n z (dHSeed q E hE b n (k, W)) 1 x (dHState q E hE b n j o) =
      .query 0 (padFin _ (wR (List.ofFn x) ++ wC (List.ofFn x))) fun y =>
        .pure (padFin _ (if List.ofFn y = wT (List.ofFn x) then decL (F n k) (List.ofFn x)
          else []), dHState q E hE b n (j + 1) o) := by
  have hwf' := hwf
  rw [wfW_eq, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at hwf'
  have hRef : ∀ L, rRef (InteractiveHandler.input n z (List.ofFn (dHSeed q E hE b n (k, W)))
      (List.ofFn (dHState q E hE b n j o)) (1 : Fin 3) (List.ofFn x) L) = false := by
    intro L
    obtain ⟨-, -, -, hX, -, -, hFlag, hRec, -, -⟩ :=
      fields_input q E hE b n z k W (i := 1) (List.ofFn x) L j o hj
    rw [rRef, hFlag, hRec, hX]
    cases o with
    | none => rfl
    | some c =>
      rw [refW_some, decide_eq_false_iff_not] at href
      rw [recBits_some, List.drop_succ_cons, List.drop_zero, Option.isSome_some, Bool.true_and,
        decide_eq_false_iff_not]
      exact fun h => href h.symm
  have hWF : ∀ L, rWF (InteractiveHandler.input n z (List.ofFn (dHSeed q E hE b n (k, W)))
      (List.ofFn (dHState q E hE b n j o)) (1 : Fin 3) (List.ofFn x) L) = true := by
    intro L
    obtain ⟨hU, -, -, hX, -, -, -, -, -, -⟩ :=
      fields_input q E hE b n z k W (i := 1) (List.ofFn x) L j o hj
    rw [rWF, hU, hX, List.length_replicate, ← wC_eq, ← wR_eq, hwf'.1, hwf'.2]
    simp
  refine InteractiveHandler.impl_of_query _ n z _ x _ 0 _ _ _
    (by rw [dHandler_perCall, PolyExpr.eval_const]) ?_ ?_
  · show dRun q E b _ = _
    obtain ⟨-, -, hI, hX, hL, -, -, -, -, -⟩ :=
      fields_input q E hE b n z k W (i := 1) (List.ofFn x) [] j o hj
    rw [dRun, hI, Fin.val_one, List.replicate_one, List.headD_cons, if_pos rfl,
      List.drop_succ_cons, List.drop_zero, List.headD_nil, if_neg Bool.false_ne_true, hRef,
      if_neg Bool.false_ne_true, hWF, if_pos rfl, hL, if_pos (decide_eq_true rfl), hX,
      ← wC_eq, ← wR_eq, ofFn_padFin_pair n hwf'.1 hwf'.2]
    rfl
  · intro y
    show dRun q E b _ = _
    simp only [Fin.val_zero, List.replicate_zero]
    obtain ⟨hU, -, hI, hX, hL, -, hFlag, hRec, hK, -⟩ :=
      fields_input q E hE b n z k W (i := 1) (List.ofFn x)
        (pairEncode (pairEncode [] (pairEncode (List.ofFn (padFin ((tagOut 0).eval n)
          (wR (List.ofFn x) ++ wC (List.ofFn x)))) (List.ofFn y))) []) j o hj
    have hY := rY_one _ _ _ hL
    have hans : (if rOK (InteractiveHandler.input n z (List.ofFn (dHSeed q E hE b n (k, W)))
        (List.ofFn (dHState q E hE b n j o)) (1 : Fin 3) (List.ofFn x)
        (pairEncode (pairEncode [] (pairEncode (List.ofFn (padFin ((tagOut 0).eval n)
          (wR (List.ofFn x) ++ wC (List.ofFn x)))) (List.ofFn y))) [])) = true then
        rDec E (InteractiveHandler.input n z (List.ofFn (dHSeed q E hE b n (k, W)))
          (List.ofFn (dHState q E hE b n j o)) (1 : Fin 3) (List.ofFn x)
          (pairEncode (pairEncode [] (pairEncode (List.ofFn (padFin ((tagOut 0).eval n)
            (wR (List.ofFn x) ++ wC (List.ofFn x)))) (List.ofFn y))) []))
        else rZero (InteractiveHandler.input n z (List.ofFn (dHSeed q E hE b n (k, W)))
          (List.ofFn (dHState q E hE b n j o)) (1 : Fin 3) (List.ofFn x)
          (pairEncode (pairEncode [] (pairEncode (List.ofFn (padFin ((tagOut 0).eval n)
            (wR (List.ofFn x) ++ wC (List.ofFn x)))) (List.ofFn y))) []))) =
        List.ofFn (padFin ((ettDout 1).eval n) (if List.ofFn y = wT (List.ofFn x) then
          decL (F n k) (List.ofFn x) else [])) := by
      rw [rOK, hY, hX, ← wT_eq]
      by_cases ht : List.ofFn y = wT (List.ofFn x)
      · rw [if_pos (decide_eq_true ht), if_pos ht, rDec, hK, hX, ← wC_eq, ← wR_eq]
        have hr : wR (List.ofFn x) = List.ofFn (padFin n (wR (List.ofFn x))) :=
          (ofFn_padFin_of_length hwf'.1).symm
        rw [hr, hFE, ← decL_eq, ofFn_padFin_of_length]
        rw [decL_eq, List.length_cons, List.length_zipWith, List.length_ofFn, hwf'.2, Nat.min_self,
          ettDout_one, PolyExpr.eval_add, PolyExpr.eval_var, PolyExpr.eval_const]
      · rw [if_neg (by rw [decide_eq_true_eq]; exact ht), if_neg ht, rZero_fields n _ hU]
    rw [dRun, hI, Fin.val_one, List.replicate_one, List.headD_cons, if_pos rfl,
      List.drop_succ_cons, List.drop_zero, List.headD_nil, if_neg Bool.false_ne_true, hRef,
      if_neg Bool.false_ne_true, hWF, if_pos rfl, hL, log_ne_nil, if_neg Bool.false_ne_true, hans,
      hFlag, hRec, recBits_fields, rNew_fields q E hE b n z k W (i := 1) _ _ j o o hj]

/-- **A malformed decryption:** from `dState j o` with a query that is not refused and not well
formed, the answer is `⊥` and the state is `dState (j + 1) o`. -/
theorem dHandler_impl_dec_nwf (x : Fin ((ettDin 1).eval n) → Bool) (j : ℕ)
    (o : Option (Fin (ettCt.eval n) → Bool)) (hj : j < q.eval n)
    (href : refW o (List.ofFn x) = false) (hwf : wfW n (List.ofFn x) = false) :
    (dHandler q E hE b).impl n z (dHSeed q E hE b n (k, W)) 1 x (dHState q E hE b n j o) =
      .pure (padFin _ [], dHState q E hE b n (j + 1) o) := by
  refine InteractiveHandler.impl_of_ret _ n z _ x _ _ _ ?_
  show dRun q E b _ = _
  obtain ⟨hU, -, hI, hX, -, -, hFlag, hRec, -, -⟩ :=
    fields_input q E hE b n z k W (i := 1) (List.ofFn x) [] j o hj
  have hRef : rRef (InteractiveHandler.input n z (List.ofFn (dHSeed q E hE b n (k, W)))
      (List.ofFn (dHState q E hE b n j o)) (1 : Fin 3) (List.ofFn x) []) = false := by
    rw [rRef, hFlag, hRec, hX]
    cases o with
    | none => rfl
    | some c =>
      rw [refW_some, decide_eq_false_iff_not] at href
      rw [recBits_some, List.drop_succ_cons, List.drop_zero, Option.isSome_some, Bool.true_and,
        decide_eq_false_iff_not]
      exact fun h => href h.symm
  have hWF : rWF (InteractiveHandler.input n z (List.ofFn (dHSeed q E hE b n (k, W)))
      (List.ofFn (dHState q E hE b n j o)) (1 : Fin 3) (List.ofFn x) []) = false := by
    rw [rWF, hU, hX, List.length_replicate, ← wC_eq, ← wR_eq, ← wfW_eq, hwf]
  rw [dRun, hI, Fin.val_one, List.replicate_one, List.headD_cons, if_pos rfl, List.drop_succ_cons,
    List.drop_zero, List.headD_nil, if_neg Bool.false_ne_true, hRef, if_neg Bool.false_ne_true,
    hWF, if_neg Bool.false_ne_true, rZero_fields n _ hU, hFlag, hRec, recBits_fields,
    rNew_fields q E hE b n z k W (i := 1) _ _ j o o hj]

/-- **A recorded challenge is repeated:** from `dState j (some c)`, a challenge is answered `c`
and the state is `dState (j + 1) (some c)`. -/
theorem dHandler_impl_challenge_some (x : Fin ((ettDin 2).eval n) → Bool) (j : ℕ)
    (c : Fin (ettCt.eval n) → Bool) (hj : j < q.eval n) :
    (dHandler q E hE b).impl n z (dHSeed q E hE b n (k, W)) 2 x (dHState q E hE b n j (some c)) =
      .pure (padFin _ (List.ofFn c), dHState q E hE b n (j + 1) (some c)) := by
  refine InteractiveHandler.impl_of_ret _ n z _ x _ _ _ ?_
  show dRun q E b _ = _
  obtain ⟨-, -, hI, -, -, -, hFlag, hRec, -, -⟩ :=
    fields_input q E hE b n z k W (i := 2) (List.ofFn x) [] j (some c) hj
  have hc : List.ofFn (padFin ((ettDout 2).eval n) (List.ofFn c)) = List.ofFn c :=
    ofFn_padFin_of_length (by rw [List.length_ofFn, ettDout_two])
  have hrec : true :: (recBits n (some c)).drop 1 = recBits n (some c) := rfl
  rw [dRun, hI, hFlag, hRec]
  simp only [show List.replicate ((2 : Fin 3) : ℕ) true = [true, true] from rfl, List.headD_cons,
    List.drop_succ_cons, List.drop_zero, if_true, Option.isSome_some]
  rw [hrec, rNew_fields q E hE b n z k W (i := 2) _ _ j (some c) (some c) hj, hc, recBits_some,
    List.drop_succ_cons, List.drop_zero]

include hFE in
/-- **The first challenge with the next tape:** from `dState j none` with `j < q(n)`, the
challenge `⟨m₀, m₁⟩` asks the outer oracle at `r ‖ c₁` with the tape `r` and
`c₁ = maskL f_k r m_b`; its answer `y` gives the ciphertext `c = ⟨r, ⟨c₁, y⟩⟩`, recorded in the
state `dState (j + 1) (some c)`. -/
theorem dHandler_impl_challenge_none (x : Fin ((ettDin 2).eval n) → Bool) (j : ℕ)
    (hj : j < q.eval n) :
    (dHandler q E hE b).impl n z (dHSeed q E hE b n (k, W)) 2 x (dHState q E hE b n j none) =
      .query 0 (padFin _ (List.ofFn (dTape q n W j hj) ++
          maskL (F n k) (dTape q n W j hj) (AdaptiveCPA.msgOf n b (List.ofFn x)))) fun y =>
        .pure (padFin _ (ctW (List.ofFn (dTape q n W j hj))
            (maskL (F n k) (dTape q n W j hj) (AdaptiveCPA.msgOf n b (List.ofFn x)))
            (List.ofFn y)),
          dHState q E hE b n (j + 1) (some (padFin (ettCt.eval n) (ctW (List.ofFn (dTape q n W j hj))
            (maskL (F n k) (dTape q n W j hj) (AdaptiveCPA.msgOf n b (List.ofFn x)))
            (List.ofFn y))))) := by
  have hmsg : (AdaptiveCPA.msgOf n b (List.ofFn x)).length = n := by
    have hx : (List.ofFn x).length = n + n := by
      rw [List.length_ofFn, ettDin_two, PolyExpr.eval_add, PolyExpr.eval_var]
    rw [AdaptiveCPA.msgOf_eq]
    cases b <;> simp [hx]
  have hm := length_maskL (F n k) (dTape q n W j hj) hmsg
  have hMsg : ∀ L, rMsg b (InteractiveHandler.input n z (List.ofFn (dHSeed q E hE b n (k, W)))
      (List.ofFn (dHState q E hE b n j none)) (2 : Fin 3) (List.ofFn x) L) =
      AdaptiveCPA.msgOf n b (List.ofFn x) := by
    intro L
    obtain ⟨hU, -, -, hX, -, -, -, -, -, -⟩ :=
      fields_input q E hE b n z k W (i := 2) (List.ofFn x) L j none hj
    rw [rMsg, hU, hX, List.length_replicate, AdaptiveCPA.msgOf_eq]
  refine InteractiveHandler.impl_of_query _ n z _ x _ 0 _ _ _
    (by rw [dHandler_perCall, PolyExpr.eval_const]) ?_ ?_
  · show dRun q E b _ = _
    obtain ⟨-, -, hI, -, hL, -, hFlag, -, hK, hN⟩ :=
      fields_input q E hE b n z k W (i := 2) (List.ofFn x) [] j none hj
    rw [dRun, hI, hFlag, hL]
    simp only [show List.replicate ((2 : Fin 3) : ℕ) true = [true, true] from rfl, List.headD_cons,
      List.drop_succ_cons, List.drop_zero, if_true, Option.isSome_none, Bool.false_eq_true,
      if_false, decide_true]
    rw [hMsg, rMask, hK, hN, mask_eval E F hFE n k, ofFn_padFin_pair n List.length_ofFn hm]
    rfl
  · intro y
    show dRun q E b _ = _
    simp only [Fin.val_zero, List.replicate_zero]
    obtain ⟨-, -, hI, -, hL, -, hFlag, -, hK, hN⟩ :=
      fields_input q E hE b n z k W (i := 2) (List.ofFn x)
        (pairEncode (pairEncode [] (pairEncode (List.ofFn (padFin ((tagOut 0).eval n)
          (List.ofFn (dTape q n W j hj) ++
            maskL (F n k) (dTape q n W j hj) (AdaptiveCPA.msgOf n b (List.ofFn x)))))
          (List.ofFn y))) []) j none hj
    have hY := rY_one _ _ _ hL
    have hlen := length_ctW_tag n (List.length_ofFn (f := dTape q n W j hj)) hm
      (by rw [List.length_ofFn, tagOut_eq, tagLen_eval] : (List.ofFn y).length = 2 * n)
    have hct : List.ofFn (padFin ((ettDout 2).eval n) (ctW (List.ofFn (dTape q n W j hj))
        (maskL (F n k) (dTape q n W j hj) (AdaptiveCPA.msgOf n b (List.ofFn x)))
        (List.ofFn y))) =
        ctW (List.ofFn (dTape q n W j hj))
          (maskL (F n k) (dTape q n W j hj) (AdaptiveCPA.msgOf n b (List.ofFn x)))
          (List.ofFn y) :=
      ofFn_padFin_of_length (by rw [hlen, ettDout_two])
    have hrec : true :: ctW (List.ofFn (dTape q n W j hj))
        (maskL (F n k) (dTape q n W j hj) (AdaptiveCPA.msgOf n b (List.ofFn x))) (List.ofFn y) =
        recBits n (some (padFin (ettCt.eval n) (ctW (List.ofFn (dTape q n W j hj))
          (maskL (F n k) (dTape q n W j hj) (AdaptiveCPA.msgOf n b (List.ofFn x)))
          (List.ofFn y)))) := by
      rw [recBits_some, ofFn_padFin_of_length hlen]
    rw [dRun, hI, hFlag, hL]
    simp only [show List.replicate ((2 : Fin 3) : ℕ) true = [true, true] from rfl, List.headD_cons,
      List.drop_succ_cons, List.drop_zero, if_true, Option.isSome_none, Bool.false_eq_true,
      if_false]
    rw [log_ne_nil, if_neg Bool.false_ne_true, hMsg, hct, rCt, rMask, hK, hN, hY,
      mask_eval E F hFE n k, ← ctW_eq, hrec,
      rNew_fields q E hE b n z k W (i := 2) _ _ j none _ hj]

end Answers

end TCSlib.Cryptography.Composability.ETTGame
