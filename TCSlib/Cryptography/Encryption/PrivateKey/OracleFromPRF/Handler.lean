/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Encryption.PrivateKey.OracleFromPRF.Games

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The handler of the PRF reduction for the §3.9 scheme

The first step of [PS10, Theorem 168.2] replaces `f_k` by a random function: a reduction with
oracle access to a function `f` runs the IND adversary and answers its queries with `f` in place
of `f_k`. This file builds that reduction as a `Games.InteractiveHandler` (`pkHandler`) with one
outer oracle (the function), so that T2 (`Games.exists_interactiveHandlerMachine`) and T4
(`Games.exists_toOracleAdversary_of_bitCodec`) make it a next-query machine.

The handler's seed is `q(n)` nonce tapes of `n` bits (`pkTapes`), one per fresh nonce; its state
counts the tapes used and records the challenge (`pkState`).
- `Enc` on `m`: ask `f` at the next tape `r`, answer `⟨r, m ⊕ f(r)⟩`, count.
- `Dec` on `w`: when open (`atk = CCA1` and no challenge yet) and `w = ⟨x, v⟩` is well formed, ask
  `f` at `x` and answer `⟨1, v ⊕ f(x)⟩`; otherwise answer `⊥`.
- `Challenge` on `⟨m₀, m₁⟩`: the first time, ask `f` at the next tape `r`, answer
  `c = ⟨r, m_b ⊕ f(r)⟩`, record `c` and count; later repeat `c`.
The finalization asks nothing and outputs the adversary's bit.

## Main definitions

* `PRFGame.ctP`, `pkDin`, `pkDout`, `pkStLen`: the lengths.
* `PRFGame.recBits`, `pkState`: the encoded state.
* `PRFGame.pkTapes`: the seed as nonce tapes.
* `PRFGame.pkHandler q atkBit b`: the handler.

## Main results

* `PRFGame.pkHandler_impl_enc`, `_impl_dec_open`, `_impl_dec_closed`, `_impl_challenge_some`,
  `_impl_challenge_none`: its answers on encoded states.
* `PRFGame.pkHandler_finish`, `pkHandler_init_eq`: the finalization and the initial state.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  Algorithm 99.1 and Theorem 168.2 (book pp. 99, 168).
-/

namespace TCSlib.Cryptography.Composability.PRFGame

open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games

/-! ### Lengths and states -/

/-- The ciphertext length `3n + 2`. -/
def ctP : PolyExpr := .add (.mul (.const 3) .var) (.const 2)

/-- `ctP.eval n = 3n + 2`. -/
theorem ctP_eval (n : ℕ) : ctP.eval n = 3 * n + 2 := by
  rw [ctP, PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const, PolyExpr.eval_const,
    PolyExpr.eval_var]

/-- The query lengths: `n`-bit messages to `Enc`, `(3n + 2)`-bit ciphertexts to `Dec`, `2n`-bit
challenge queries. -/
def pkDin : Fin 3 → PolyExpr
  | 0 => .var
  | 1 => ctP
  | 2 => .add .var .var

/-- `Enc` queries have `n` bits: `pkDin 0 = var`. -/
theorem pkDin_zero : pkDin 0 = .var := rfl

/-- `Dec` queries have `3n + 2` bits: `pkDin 1 = ctP`. -/
theorem pkDin_one : pkDin 1 = ctP := rfl

/-- Challenge queries have `2n` bits: `pkDin 2 = var + var`. -/
theorem pkDin_two : pkDin 2 = .add .var .var := rfl

/-- The answer lengths: ciphertexts, `(n + 1)`-bit decryption answers, ciphertexts. -/
def pkDout : Fin 3 → PolyExpr
  | 0 => ctP
  | 1 => .add .var (.const 1)
  | 2 => ctP

/-- `Enc` answers are ciphertexts: `pkDout 0 = ctP`. -/
theorem pkDout_zero : pkDout 0 = ctP := rfl

/-- `Dec` answers have `n + 1` bits: `pkDout 1 = var + 1`. -/
theorem pkDout_one : pkDout 1 = .add .var (.const 1) := rfl

/-- Challenge answers are ciphertexts: `pkDout 2 = ctP`. -/
theorem pkDout_two : pkDout 2 = ctP := rfl

/-- The outer oracle: `n`-bit queries and answers. -/
abbrev pkOut : Fin 1 → PolyExpr := fun _ => .var

/-- `pkOut j = var`. -/
theorem pkOut_eq (j : Fin 1) : pkOut j = .var := rfl

variable (q : PolyExpr)

/-- The state length `2q + 3 + (3n + 2)`. -/
def pkStLen : PolyExpr := .add (.add (.mul (.const 2) q) (.const 3)) ctP

/-- `pkStLen q = 2q + 3 + ctP`. -/
theorem pkStLen_eq : pkStLen q = .add (.add (.mul (.const 2) q) (.const 3)) ctP := rfl

/-- The record of the challenge: `1 :: c` once recorded, `0^{1 + ct(n)}` before. -/
def recBits (n : ℕ) : Option (Fin (ctP.eval n) → Bool) → List Bool
  | none => false :: List.replicate (ctP.eval n) false
  | some c => true :: List.ofFn c

/-- `recBits n none = 0^{1 + ct(n)}`. -/
theorem recBits_none (n : ℕ) : recBits n none = false :: List.replicate (ctP.eval n) false := rfl

/-- `recBits n (some c) = 1 :: ⟦c⟧`. -/
theorem recBits_some (n : ℕ) (c : Fin (ctP.eval n) → Bool) :
    recBits n (some c) = true :: List.ofFn c := rfl

/-- The record has `1 + ct(n)` bits. -/
theorem length_recBits (n : ℕ) (o : Option (Fin (ctP.eval n) → Bool)) :
    (recBits n o).length = ctP.eval n + 1 := by
  cases o with
  | none => rw [recBits_none, List.length_cons, List.length_replicate]
  | some c => rw [recBits_some, List.length_cons, List.length_ofFn]

/-- **The encoded state** after `j` fresh nonces, with the challenge record `o`:
`⟨1^j, recBits o⟩`, padded with `false` to the state length. -/
def pkState (n j : ℕ) (o : Option (Fin (ctP.eval n) → Bool)) :
    Fin ((pkStLen q).eval n) → Bool :=
  padFin _ (pairEncode (List.replicate j true) (recBits n o))

/-- `pkState q n j o = padFin _ ⟨1^j, recBits n o⟩`. -/
theorem pkState_eq (n j : ℕ) (o : Option (Fin (ctP.eval n) → Bool)) :
    pkState q n j o = padFin _ (pairEncode (List.replicate j true) (recBits n o)) :=
  rfl

/-- **The seed as nonce tapes:** `q(n) · n` bits as `q(n)` blocks of `n` bits. -/
def pkTapes (n : ℕ) : (Fin ((q.mul .var).eval n) → Bool) ≃ (Fin (q.eval n) → Fin n → Bool) :=
  (Equiv.arrowCongr (finCongr (by rw [PolyExpr.eval_mul, PolyExpr.eval_var]))
    (Equiv.refl Bool)).trans (EnsembleLemmas.blocks (q.eval n) n)

/-- **Bit `k` of tape `j` is bit `j·n + k` of the seed:**
`pkTapes q n ω j k = ω (finProdFinEquiv (j, k))`, read at the seed's length. -/
theorem pkTapes_apply (n : ℕ) (ω : Fin ((q.mul .var).eval n) → Bool) (j : Fin (q.eval n))
    (k : Fin n) :
    pkTapes q n ω j k = ω (Fin.cast (by rw [PolyExpr.eval_mul, PolyExpr.eval_var])
      (finProdFinEquiv (j, k))) := by
  unfold pkTapes
  rw [Equiv.trans_apply, EnsembleLemmas.blocks_apply]
  rfl

/-- **Tape `j` is the `j`-th block of the seed:** `⟦pkTapes q n ω j⟧ = (⟦ω⟧.drop (j·n)).take n`.

**Proof sketch.** Position `k` of block `j` is position `j·n + k` of `ω` (`blocks_apply`,
`finProdFinEquiv_apply_val`), which is position `k` of the dropped and truncated list. -/
theorem ofFn_pkTapes (n : ℕ) (ω : Fin ((q.mul .var).eval n) → Bool) (j : Fin (q.eval n)) :
    List.ofFn (pkTapes q n ω j) = ((List.ofFn ω).drop (j * n)).take n := by
  have hlen : (q.mul .var).eval n = q.eval n * n := by rw [PolyExpr.eval_mul, PolyExpr.eval_var]
  have hj := j.isLt
  have hle : (j : ℕ) * n + n ≤ q.eval n * n := by
    have := Nat.mul_le_mul_right n (Nat.succ_le_of_lt hj)
    rw [Nat.succ_mul] at this
    exact this
  refine List.ext_getElem ?_ fun k h₁ h₂ => ?_
  · simp only [List.length_ofFn, List.length_take, List.length_drop]
    omega
  · have hpt : ∀ k' : Fin n, pkTapes q n ω j k' =
        ω (Fin.cast hlen.symm (finProdFinEquiv (j, k'))) := fun k' => pkTapes_apply q n ω j k'
    simp only [List.getElem_ofFn, List.getElem_take, List.getElem_drop, hpt]
    congr 1
    refine Fin.ext ?_
    rw [Fin.coe_cast, finProdFinEquiv_apply_val]
    show k + n * j = j * n + k
    rw [Nat.mul_comm]
    omega

/-! ### Strings -/

/-- `⟦padFin k a⟧ = padL k a`. -/
private theorem ofFn_padFin_eq_padL (k : ℕ) (a : List Bool) :
    List.ofFn (padFin k a) = EnsembleLemmas.padL k a := by
  rw [EnsembleLemmas.padL_eq, ofFn_padFin_eq_take]

/-- The fields of an encoded state with `j ≤ q(n)`: the count `1^j`, the flag and the record. -/
private theorem fields_pkState (n j : ℕ) (o : Option (Fin (ctP.eval n) → Bool))
    (hj : j ≤ q.eval n) :
    pairFstD (List.ofFn (pkState q n j o)) = List.replicate j true ∧
      (pairSndD (List.ofFn (pkState q n j o))).headD false = o.isSome ∧
      ((pairSndD (List.ofFn (pkState q n j o))).drop 1).take (ctP.eval n) =
        (recBits n o).drop 1 := by
  have hlen : (pairEncode (List.replicate j true) (recBits n o)).length ≤ (pkStLen q).eval n := by
    rw [length_pairEncode, List.length_replicate, length_recBits, pkStLen_eq, PolyExpr.eval_add,
      PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const, PolyExpr.eval_const]
    omega
  rw [pkState_eq, Collection.ofFn_padFin_of_le hlen, ← GGMRed.pairEncode_append_right]
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

/-- The parameter `1^n` of a round input `⟨⟨1^n, ⟨z, ω⟩⟩, ⟨s, ⟨⟨1^i, x⟩, L⟩⟩⟩`. -/
private def rU (w : List Bool) : List Bool := pairFstD (pairFstD w)
/-- The seed `ω`. -/
private def rW (w : List Bool) : List Bool := pairSndD (pairSndD (pairFstD w))
/-- The state `s`. -/
private def rS (w : List Bool) : List Bool := pairFstD (pairSndD w)
/-- The oracle index `1^i`. -/
private def rI (w : List Bool) : List Bool := pairFstD (pairFstD (pairSndD (pairSndD w)))
/-- The query `x`. -/
private def rX (w : List Bool) : List Bool := pairSndD (pairFstD (pairSndD (pairSndD w)))
/-- The outer log `L` of the call. -/
private def rL (w : List Bool) : List Bool := pairSndD (pairSndD (pairSndD w))
/-- The count `1^j` of the state. -/
private def rCnt (w : List Bool) : List Bool := pairFstD (rS w)
/-- The challenge flag of the state. -/
private def rFlag (w : List Bool) : Bool := (pairSndD (rS w)).headD false
/-- The recorded challenge of the state. -/
private def rRec (w : List Bool) : List Bool :=
  ((pairSndD (rS w)).drop 1).take (ctP.eval (rU w).length)
/-- The outer answer recorded in the log `⟨⟨[], ⟨x, y⟩⟩, []⟩`. -/
private def rY (w : List Bool) : List Bool := pairSndD (pairSndD (pairFstD (rL w)))
/-- Tape `j` of the seed. -/
private def rNonce (w : List Bool) : List Bool :=
  ((rW w).drop ((rCnt w).length * (rU w).length)).take (rU w).length
/-- The ciphertext `⟨r, m ⊕ y⟩` with the tape `r` and the outer answer `y`. -/
private def rCt (w m : List Bool) : List Bool :=
  pairEncode (rNonce w) (List.zipWith xor m (rY w))
/-- The selected challenge message `m_b`. -/
private def rMsg (b : Bool) (w : List Bool) : List Bool :=
  if b then (rX w).drop (rU w).length else (rX w).take (rU w).length
/-- Whether the decryption query `⟨x, v⟩` is well formed. -/
private def rWF (w : List Bool) : Bool :=
  decide ((pairFstD (rX w)).length = (rU w).length) &&
    decide ((pairSndD (rX w)).length = (rU w).length)
/-- The new state after a fresh nonce: count `j + 1`, record `t`. -/
private def rNew (w t : List Bool) : List Bool :=
  EnsembleLemmas.padL ((pkStLen q).eval (rU w).length) (pairEncode (true :: rCnt w) t)

/-- **One round of the handler** (see the module docstring), for the attack bit `atkBit` (`true`
for CCA1) and the challenge bit `b`. A first round asks the outer oracle; the second round, with
the answer `y` in the log, returns the answer and the new state. -/
private def pkRun (atkBit b : Bool) (w : List Bool) : List Bool :=
  if (rI w).headD false then
    if ((rI w).drop 1).headD false then
      if rFlag w then pairEncode [true] (rRec w ++ rS w)
      else if decide (rL w = []) then pairEncode [false] (pairEncode [] (rNonce w))
      else pairEncode [true] (rCt w (rMsg b w) ++ rNew q w (true :: rCt w (rMsg b w)))
    else
      if atkBit && !rFlag w && rWF w then
        if decide (rL w = []) then pairEncode [false] (pairEncode [] (pairFstD (rX w)))
        else pairEncode [true] ((true :: List.zipWith xor (pairSndD (rX w)) (rY w)) ++ rS w)
      else pairEncode [true]
        (List.replicate ((PolyExpr.add .var (.const 1)).eval (rU w).length) false ++ rS w)
  else
    if decide (rL w = []) then pairEncode [false] (pairEncode [] (rNonce w))
    else pairEncode [true] (rCt w (rX w) ++ rNew q w (rFlag w :: rRec w))

/-- The round function is polynomial-time.

**Proof sketch.** Pair projections; the tape by `unaryMulPair`, `dropPrefixByLength` and
`pairTakePoly`; the exclusive-or by `pairXor`; the well-formedness test by `lenEq_poly`; the
padded new state by `padL`; and `polyTimeComputable_ite` for the cases. -/
private theorem polyTimeComputable_pkRun (atkBit b : Bool) :
    PolyTimeComputable (pkRun q atkBit b) := by
  have hF := polyTimeComputable_pairFstD
  have hD := polyTimeComputable_pairSndD
  have hU : PolyTimeComputable rU := hF.comp hF
  have hW : PolyTimeComputable rW := hD.comp (hD.comp hF)
  have hS : PolyTimeComputable rS := hF.comp hD
  have hI : PolyTimeComputable rI := hF.comp (hF.comp (hD.comp hD))
  have hX : PolyTimeComputable rX := hD.comp (hF.comp (hD.comp hD))
  have hL : PolyTimeComputable rL := hD.comp (hD.comp hD)
  have hCnt : PolyTimeComputable rCnt := hF.comp hS
  have hT : PolyTimeComputable fun w => pairSndD (rS w) := hD.comp hS
  have hFlag : PolyTimeComputable fun w => [rFlag w] := polyTimeComputable_headD.comp hT
  have hRec : PolyTimeComputable rRec :=
    ((polyTimeComputable_pairTakePoly ctP).comp
      (hU.pairEncode (polyTimeComputable_tail.comp hT))).congr fun w => by
        simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]; rfl
  have hY : PolyTimeComputable rY := hD.comp (hD.comp (hF.comp hL))
  have hOff : PolyTimeComputable fun w =>
      List.replicate ((rCnt w).length * (rU w).length) true :=
    (OneWay.polyTimeComputable_unaryMulPair.comp (hCnt.pairEncode hU)).congr fun w => by
      simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]
  have hDrop : PolyTimeComputable fun w => (rW w).drop ((rCnt w).length * (rU w).length) :=
    (polyTimeComputable_dropPrefixByLength.comp (hOff.pairEncode hW)).congr fun w => by
      simp only [Function.comp_apply, PrefixByLength.drop_def, pairFstD_pairEncode,
        pairSndD_pairEncode, List.length_replicate]
  have hNonce : PolyTimeComputable rNonce :=
    ((polyTimeComputable_pairTakePoly .var).comp (hU.pairEncode hDrop)).congr fun w => by
      simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode,
        PolyExpr.eval_var]; rfl
  have hXor : ∀ {m : List Bool → List Bool}, PolyTimeComputable m →
      PolyTimeComputable fun w => List.zipWith xor (m w) (rY w) := fun hm =>
    (polyTimeComputable_pairXor.comp (hm.pairEncode hY)).congr fun w => by
      simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]
  have hCt : ∀ {m : List Bool → List Bool}, PolyTimeComputable m →
      PolyTimeComputable fun w => rCt w (m w) := fun hm => hNonce.pairEncode (hXor hm)
  have hMsg : PolyTimeComputable (rMsg b) :=
    polyTimeComputable_ite (polyTimeComputable_const [b])
      (((polyTimeComputable_pairDropPoly .var).comp (hU.pairEncode hX)).congr fun w => by
        simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode,
          PolyExpr.eval_var])
      (((polyTimeComputable_pairTakePoly .var).comp (hU.pairEncode hX)).congr fun w => by
        simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode,
          PolyExpr.eval_var])
  have hWF : PolyTimeComputable fun w => [rWF w] :=
    polyTimeComputable_and (EffFill.lenEq_poly (hF.comp hX) hU)
      (EffFill.lenEq_poly (hD.comp hX) hU)
  have hNew : ∀ {t : List Bool → List Bool}, PolyTimeComputable t →
      PolyTimeComputable fun w => rNew q w (t w) := fun ht =>
    EnsembleLemmas.polyTimeComputable_padL (pkStLen q) hU
      (((polyTimeComputable_const [true]).append hCnt).pairEncode ht)
  have hRet : ∀ {f : List Bool → List Bool}, PolyTimeComputable f →
      PolyTimeComputable fun w => pairEncode [true] (f w) := fun hf =>
    (polyTimeComputable_const [true]).pairEncode hf
  have hQry : ∀ {f : List Bool → List Bool}, PolyTimeComputable f →
      PolyTimeComputable fun w => pairEncode [false] (pairEncode [] (f w)) := fun hf =>
    (polyTimeComputable_const [false]).pairEncode ((polyTimeComputable_const []).pairEncode hf)
  have cNil : PolyTimeComputable fun w => [decide (rL w = [])] := polyTimeComputable_isNil.comp hL
  have cOpen : PolyTimeComputable fun w => [atkBit && !rFlag w && rWF w] :=
    polyTimeComputable_and (polyTimeComputable_and (polyTimeComputable_const [atkBit])
      (polyTimeComputable_not hFlag)) hWF
  have hZeros : PolyTimeComputable fun w =>
      List.replicate ((PolyExpr.add .var (.const 1)).eval (rU w).length) false :=
    EnsembleLemmas.polyTimeComputable_zeros _ hU
  have hChal := polyTimeComputable_ite hFlag (hRet (hRec.append hS))
    (polyTimeComputable_ite cNil (hQry hNonce)
      (hRet ((hCt hMsg).append (hNew ((polyTimeComputable_const [true]).append (hCt hMsg))))))
  have hDec := polyTimeComputable_ite cOpen
    (polyTimeComputable_ite cNil (hQry (hF.comp hX))
      (hRet (((polyTimeComputable_const [true]).append (hXor (hD.comp hX))).append hS)))
    (hRet (hZeros.append hS))
  have hKeep : PolyTimeComputable fun w => rFlag w :: rRec w :=
    (hFlag.append hRec).congr fun _ => rfl
  have hEnc := polyTimeComputable_ite cNil (hQry hNonce) (hRet ((hCt hX).append (hNew hKeep)))
  exact polyTimeComputable_ite (polyTimeComputable_headD.comp hI)
    (polyTimeComputable_ite (polyTimeComputable_headD.comp (polyTimeComputable_tail.comp hI))
      hChal hDec) hEnc

/-- The finalization's round: output `A`'s bit, `⟨[true], a⟩` on `⟨ctx, ⟨s, ⟨a, L⟩⟩⟩`. -/
private def pkFin (w : List Bool) : List Bool :=
  pairEncode [true] (pairFstD (pairSndD (pairSndD w)))

/-- The finalization's round is polynomial-time. -/
private theorem polyTimeComputable_pkFin : PolyTimeComputable pkFin :=
  (polyTimeComputable_const [true]).pairEncode
    (polyTimeComputable_pairFstD.comp
      (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD))

/-! ### The handler -/

/-- **The handler of the PRF reduction** for the budget `q`, the attack bit `atkBit` (`true` for
CCA1, `false` for CPA) and the challenge bit `b`: state `pkState j o` (initially `j = 0` and no
record), seed `q · n` bits (the tapes `pkTapes`), one outer call per inner query, the adversary
run on the reduction input (ignored), and the finalization outputting the adversary's bit. -/
noncomputable def pkHandler (atkBit b : Bool) :
    InteractiveHandler 3 pkDin pkDout 1 pkOut pkOut where
  stateLen := pkStLen q
  seedLen := q.mul .var
  perCall := .const 1
  init n := pkState q n 0 none
  run := pkRun q atkBit b
  poly := polyTimeComputable_pkRun q atkBit b
  advIn ctx := pairFstD (pairSndD ctx)
  advIn_poly := polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD
  outLen := .const 1
  finCall := .const 0
  finRun := pkFin
  finRun_poly := polyTimeComputable_pkFin

attribute [simps (config := { isSimp := false }) stateLen seedLen perCall init outLen finCall]
  pkHandler

/-- The handler's initial state is the empty count and no record:
`(pkHandler q atkBit b).init n = pkState q n 0 none`. -/
theorem pkHandler_init_eq (atkBit b : Bool) (n : ℕ) :
    (pkHandler q atkBit b).init n = pkState q n 0 none :=
  rfl

/-- The handler's seed as nonce tapes (`pkTapes`), at the handler's seed type. -/
def pkSeedTapes (atkBit b : Bool) (n : ℕ) :
    (Fin ((pkHandler q atkBit b).seedLen.eval n) → Bool) ≃ (Fin (q.eval n) → Fin n → Bool) :=
  pkTapes q n

/-- The encoded state at the handler's state type: `pkHState q atkBit b n j o = pkState q n j o`. -/
def pkHState (atkBit b : Bool) (n j : ℕ) (o : Option (Fin (ctP.eval n) → Bool)) :
    Fin ((pkHandler q atkBit b).stateLen.eval n) → Bool :=
  pkState q n j o

/-- `pkHState q atkBit b n j o = pkState q n j o`. -/
theorem pkHState_eq (atkBit b : Bool) (n j : ℕ) (o : Option (Fin (ctP.eval n) → Bool)) :
    pkHState q atkBit b n j o = pkState q n j o :=
  rfl

/-- The initial state is the encoded `(0, none)`: `(pkHandler q atkBit b).init n =
pkHState q atkBit b n 0 none`. -/
theorem pkHandler_init_hstate (atkBit b : Bool) (n : ℕ) :
    (pkHandler q atkBit b).init n = pkHState q atkBit b n 0 none :=
  rfl

/-- `pkSeedTapes q atkBit b n = pkTapes q n`. -/
theorem pkSeedTapes_eq (atkBit b : Bool) (n : ℕ) : pkSeedTapes q atkBit b n = pkTapes q n :=
  rfl

/-- The finalization outputs the adversary's bit and asks nothing:
`(pkHandler q atkBit b).finish n z ω s a = pure (padFin _ ⟦a⟧)`. -/
theorem pkHandler_finish (atkBit b : Bool) (n : ℕ) (z : List Bool)
    (ω : Fin ((pkHandler q atkBit b).seedLen.eval n) → Bool)
    (s : Fin ((pkHandler q atkBit b).stateLen.eval n) → Bool)
    (a : Fin ((PolyExpr.const 1).eval n) → Bool) :
    (pkHandler q atkBit b).finish n z ω s a =
      .pure (padFin ((pkHandler q atkBit b).outLen.eval n) (List.ofFn a)) := by
  rw [InteractiveHandler.finish_eq]
  have h0 : (pkHandler q atkBit b).finCall.eval n = 0 := by
    rw [pkHandler_finCall, PolyExpr.eval_const]
  rw [h0]
  refine buildComp_zero_of_ret ?_
  show decodeBitMove _ _ _ (pkFin _) = _
  rw [pkFin, InteractiveHandler.finInput_eq, pairSndD_pairEncode, pairSndD_pairEncode,
    pairFstD_pairEncode]
  have hw : List.ofFn (padFin ((pkHandler q atkBit b).outLen.eval n) (List.ofFn a)) =
      List.ofFn a :=
    GGMRed.ofFn_padFin_of_length (by rw [List.length_ofFn, pkHandler_outLen])
  exact (congrArg (fun w => decodeBitMove _ _ _ (pairEncode [true] w)) hw).symm.trans
    (decodeBitMove_ret _ _ _ _)

/-! ### Answers of the handler -/

section Answers

variable (atkBit b : Bool) (n : ℕ) (z : List Bool)
  (ω : Fin ((pkHandler q atkBit b).seedLen.eval n) → Bool)

/-- A call whose first round returns `y ‖ s'` is answered `y` with new state `s'`. -/
private theorem impl_of_ret {i : Fin 3} (x : Fin ((pkDin i).eval n) → Bool)
    (s : Fin ((pkStLen q).eval n) → Bool) (y : Fin ((pkDout i).eval n) → Bool)
    (s' : Fin ((pkStLen q).eval n) → Bool)
    (h : pkRun q atkBit b (InteractiveHandler.input n z (List.ofFn ω) (List.ofFn s) i
      (List.ofFn x) []) = pairEncode [true] (List.ofFn y ++ List.ofFn s')) :
    (pkHandler q atkBit b).impl n z ω i x s = .pure (y, s') := by
  rw [InteractiveHandler.impl_apply, InteractiveHandler.call_eq, pkHandler_perCall,
    PolyExpr.eval_const]
  rw [buildComp_succ_of_ret (a := Fin.append y s') (by
    show decodeBitMove _ _ _ (pkRun q atkBit b _) = _
    rw [MachineCodec.encodeLog_nil, h, ← List.ofFn_fin_append]
    exact decodeBitMove_ret _ _ _ _), OracleComp.pure_bind]
  congr 2
  · funext j
    exact Fin.append_left y s' j
  · funext j
    exact Fin.append_right y s' j

/-- The outer log after one outer query `x'` answered `y`. -/
private theorem encodeLog_one (x' y : Fin ((pkOut 0).eval n) → Bool) :
    (bitCodec (fun j => (pkOut j).eval n) (fun j => (pkOut j).eval n) 0).encodeLog
        ([] ++ [⟨0, x', y⟩]) =
      pairEncode (pairEncode [] (pairEncode (List.ofFn x') (List.ofFn y))) [] := by
  rw [List.nil_append, MachineCodec.encodeLog_cons, MachineCodec.encodeLog_nil,
    bitCodec_encodeEntry]
  rfl

/-- A call whose first round asks `x'` of the outer oracle, and whose second round, with the
answer `y` in the log, returns `ans y ‖ s' y`, is the query `x'` followed by `(ans y, s' y)`. -/
private theorem impl_of_query {i : Fin 3} (x : Fin ((pkDin i).eval n) → Bool)
    (s : Fin ((pkStLen q).eval n) → Bool) (x' : Fin ((pkOut 0).eval n) → Bool)
    (ans : (Fin ((pkOut 0).eval n) → Bool) → Fin ((pkDout i).eval n) → Bool)
    (s' : (Fin ((pkOut 0).eval n) → Bool) → Fin ((pkStLen q).eval n) → Bool)
    (h1 : pkRun q atkBit b (InteractiveHandler.input n z (List.ofFn ω) (List.ofFn s) i
      (List.ofFn x) []) = pairEncode [false] (pairEncode [] (List.ofFn x')))
    (h2 : ∀ y, pkRun q atkBit b (InteractiveHandler.input n z (List.ofFn ω) (List.ofFn s) i
      (List.ofFn x) (pairEncode (pairEncode [] (pairEncode (List.ofFn x') (List.ofFn y))) [])) =
        pairEncode [true] (List.ofFn (ans y) ++ List.ofFn (s' y))) :
    (pkHandler q atkBit b).impl n z ω i x s =
      .query 0 x' fun y => .pure (ans y, s' y) := by
  rw [InteractiveHandler.impl_apply, InteractiveHandler.call_eq, pkHandler_perCall,
    PolyExpr.eval_const]
  rw [buildComp_succ_of_query (i := 0) (x := x') (by
    show decodeBitMove _ _ _ (pkRun q atkBit b _) = _
    rw [MachineCodec.encodeLog_nil, h1]
    exact decodeBitMove_query (fun j => (pkOut j).eval n) (fun j => (pkOut j).eval n) _ 0 x'),
    OracleComp.query_bind]
  congr 1
  funext y
  rw [buildComp_zero_of_ret (a := Fin.append (ans y) (s' y)) (by
    show decodeBitMove _ _ _ (pkRun q atkBit b _) = _
    rw [encodeLog_one, h2, ← List.ofFn_fin_append]
    exact decodeBitMove_ret _ _ _ _), OracleComp.pure_bind]
  congr 2
  · funext k
    exact Fin.append_left (ans y) (s' y) k
  · funext k
    exact Fin.append_right (ans y) (s' y) k

/-- The round input of a call, field by field, on an encoded state with `j ≤ q(n)`. -/
private theorem fields_input {i : Fin 3} (x L : List Bool) (j : ℕ)
    (o : Option (Fin (ctP.eval n) → Bool)) (hj : j ≤ q.eval n) :
    let w := InteractiveHandler.input n z (List.ofFn ω) (List.ofFn (pkState q n j o)) i x L
    rU w = List.replicate n true ∧ rW w = List.ofFn ω ∧
      rS w = List.ofFn (pkState q n j o) ∧ rI w = List.replicate i true ∧ rX w = x ∧
      rL w = L ∧ rCnt w = List.replicate j true ∧ rFlag w = o.isSome ∧
      rRec w = (recBits n o).drop 1 := by
  obtain ⟨h₁, h₂, h₃⟩ := fields_pkState q n j o hj
  simp only [InteractiveHandler.input_eq, rU, rW, rS, rI, rX, rL, rCnt, rFlag, rRec,
    pairFstD_pairEncode, pairSndD_pairEncode, List.length_replicate, h₁, h₂, h₃, and_self]

/-- The tape at the count `j < q(n)` is the `j`-th block of the seed. -/
private theorem rNonce_fields {i : Fin 3} (x L : List Bool) (j : ℕ)
    (o : Option (Fin (ctP.eval n) → Bool)) (hj : j < q.eval n) :
    rNonce (InteractiveHandler.input n z (List.ofFn ω) (List.ofFn (pkState q n j o)) i x L) =
      List.ofFn (pkSeedTapes q atkBit b n ω ⟨j, hj⟩) := by
  obtain ⟨hU, hW, -, -, -, -, hCnt, -, -⟩ := fields_input q atkBit b n z ω (i := i) x L j o hj.le
  rw [rNonce, hU, hW, hCnt, List.length_replicate, List.length_replicate, pkSeedTapes_eq]
  exact (ofFn_pkTapes q n ω ⟨j, hj⟩).symm

/-- The new state after a fresh nonce from `pkState j o`, with record `t`. -/
private theorem rNew_fields {i : Fin 3} (x L : List Bool) (j : ℕ)
    (o o' : Option (Fin (ctP.eval n) → Bool)) (hj : j ≤ q.eval n) :
    rNew q (InteractiveHandler.input n z (List.ofFn ω) (List.ofFn (pkState q n j o)) i x L)
        (recBits n o') = List.ofFn (pkState q n (j + 1) o') := by
  obtain ⟨hU, -, -, -, -, -, hCnt, -, -⟩ := fields_input q atkBit b n z ω (i := i) x L j o hj
  rw [rNew, hU, hCnt, List.length_replicate, pkState_eq, ofFn_padFin_eq_padL, List.replicate_succ]

/-- The flag and the record rebuild the record bits: `rFlag :: rRec = recBits o`. -/
private theorem recBits_fields (o : Option (Fin (ctP.eval n) → Bool)) :
    o.isSome :: (recBits n o).drop 1 = recBits n o := by
  cases o <;> rfl

/-- The outer answer recorded in a one-entry log. -/
private theorem rY_one (w : List Bool) (x' y : List Bool)
    (hL : rL w = pairEncode (pairEncode [] (pairEncode x' y)) []) : rY w = y := by
  rw [rY, hL, pairFstD_pairEncode, pairSndD_pairEncode, pairSndD_pairEncode]

/-- The index word of oracle `1`. -/
private theorem replicate_one : List.replicate ((1 : Fin 3) : ℕ) true = [true] := rfl

/-- The index word of oracle `2`. -/
private theorem replicate_two : List.replicate ((2 : Fin 3) : ℕ) true = [true, true] := rfl

/-- The index word of oracle `0`. -/
private theorem replicate_zero' : List.replicate ((0 : Fin 3) : ℕ) true = [] := rfl

/-- A one-entry log is not empty. -/
private theorem log_ne_nil (x' y : List Bool) :
    decide (pairEncode (pairEncode [] (pairEncode x' y)) [] = []) = false :=
  decide_eq_false (pairEncode_ne_nil _ _)

/-- **Encryption with the next tape:** from `pkState j o` with `j < q(n)`, the query `m` asks the
outer oracle at the tape `r = T_j`, and its answer `y` gives the ciphertext `⟨r, m ⊕ y⟩` and the
state `pkState (j + 1) o`.

**Proof sketch.** Read the round input field by field (`fields_input`); the first round, with an
empty log, asks the outer oracle at the tape `T_j` (`rNonce_fields`); the second, with the answer
`y` in the log (`rY_one`), returns `⟨T_j, m ⊕ y⟩` and the state with count `j + 1`
(`rNew_fields`); `impl_of_query` assembles the two rounds. -/
theorem pkHandler_impl_enc (x : Fin ((pkDin 0).eval n) → Bool) (j : ℕ)
    (o : Option (Fin (ctP.eval n) → Bool)) (hj : j < q.eval n) :
    (pkHandler q atkBit b).impl n z ω 0 x (pkState q n j o) =
      .query 0 (padFin _ (List.ofFn (pkSeedTapes q atkBit b n ω ⟨j, hj⟩))) fun y =>
        .pure (padFin _ (ctOf (pkSeedTapes q atkBit b n ω ⟨j, hj⟩) (List.ofFn x)
          (padFin n (List.ofFn y))), pkState q n (j + 1) o) := by
  have hn : (pkOut 0).eval n = n := by rw [pkOut_eq, PolyExpr.eval_var]
  have hT : List.ofFn (padFin ((pkOut 0).eval n)
      (List.ofFn (pkSeedTapes q atkBit b n ω ⟨j, hj⟩))) =
      List.ofFn (pkSeedTapes q atkBit b n ω ⟨j, hj⟩) :=
    GGMRed.ofFn_padFin_of_length (by rw [List.length_ofFn, hn])
  refine impl_of_query q atkBit b n z ω x _ _ _ _ ?_ ?_
  · obtain ⟨-, -, -, hI, -, hL, -, -, -⟩ :=
      fields_input q atkBit b n z ω (i := 0) (List.ofFn x) [] j o hj.le
    rw [pkRun, hI, hL, hT, rNonce_fields q atkBit b n z ω (i := 0) _ _ j o hj]
    rfl
  · intro y
    obtain ⟨-, -, -, hI, hX, hL, -, hFlag, hRec⟩ :=
      fields_input q atkBit b n z ω (i := 0) (List.ofFn x)
        (pairEncode (pairEncode [] (pairEncode (List.ofFn (padFin ((pkOut 0).eval n)
          (List.ofFn (pkSeedTapes q atkBit b n ω ⟨j, hj⟩)))) (List.ofFn y))) []) j o hj.le
    have hY := rY_one _ _ _ hL
    have hy : List.ofFn (padFin n (List.ofFn y)) = List.ofFn y :=
      GGMRed.ofFn_padFin_of_length (by rw [List.length_ofFn, hn])
    have hct : List.ofFn (padFin ((pkDout 0).eval n) (ctOf (pkSeedTapes q atkBit b n ω ⟨j, hj⟩)
        (List.ofFn x) (padFin n (List.ofFn y)))) =
        ctOf (pkSeedTapes q atkBit b n ω ⟨j, hj⟩) (List.ofFn x) (padFin n (List.ofFn y)) :=
      GGMRed.ofFn_padFin_of_length (by
        rw [length_ctOf _ (by rw [List.length_ofFn, pkDin_zero, PolyExpr.eval_var]), pkDout_zero,
          ctP_eval])
    rw [pkRun, hI, replicate_zero', List.headD_nil, if_neg Bool.false_ne_true, hL, log_ne_nil,
      if_neg Bool.false_ne_true, hct, rCt, rNonce_fields q atkBit b n z ω (i := 0) _ _ j o hj,
      hX, hY, hFlag, hRec, recBits_fields, rNew_fields q atkBit b n z ω (i := 0) _ _ j o o hj.le,
      ctOf_eq, hy]

/-- **Open decryption:** if the oracle is open (`atkBit`, no record) and `w = ⟦x⟧ = ⟨x₀, v⟩` is
well formed, the query asks the outer oracle at `x₀`, and its answer `y` gives `⟨1, v ⊕ y⟩`; the
state is kept.

**Proof sketch.** As for `pkHandler_impl_enc`: the open test reads `atkBit`, the flag and the
well-formedness of `⟦x⟧` (`fields_input`); the first round asks the outer oracle at `x₀`, the second
returns `⟨1, v ⊕ y⟩` with the state unchanged (`impl_of_query`). -/
theorem pkHandler_impl_dec_open (x : Fin ((pkDin 1).eval n) → Bool) (j : ℕ)
    (o : Option (Fin (ctP.eval n) → Bool)) (hj : j ≤ q.eval n)
    (hop : (atkBit && !o.isSome && decWF n (List.ofFn x)) = true) :
    (pkHandler q atkBit b).impl n z ω 1 x (pkState q n j o) =
      .query 0 (padFin _ (pairFstD (List.ofFn x))) fun y =>
        .pure (padFin _ (true :: List.zipWith xor (pairSndD (List.ofFn x)) (List.ofFn y)),
          pkState q n j o) := by
  have hn : (pkOut 0).eval n = n := by rw [pkOut_eq, PolyExpr.eval_var]
  have hwf : decWF n (List.ofFn x) = true := by
    simp only [Bool.and_eq_true] at hop
    exact hop.2
  rw [decWF_eq, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at hwf
  have hx0 : List.ofFn (padFin ((pkOut 0).eval n) (pairFstD (List.ofFn x))) =
      pairFstD (List.ofFn x) := GGMRed.ofFn_padFin_of_length (by rw [hwf.1, hn])
  have hc : ((1 : Fin 3) : ℕ) = 1 := rfl
  refine impl_of_query q atkBit b n z ω x _ _ _ _ ?_ ?_
  · obtain ⟨hU, -, -, hI, hX, hL, -, hFlag, -⟩ :=
      fields_input q atkBit b n z ω (i := 1) (List.ofFn x) [] j o hj
    have hWF : rWF (InteractiveHandler.input n z (List.ofFn ω) (List.ofFn (pkState q n j o))
        (1 : Fin 3)
        (List.ofFn x) []) = decWF n (List.ofFn x) := by
      rw [rWF, hU, hX, List.length_replicate, decWF_eq]
    rw [pkRun, hI, replicate_one, hFlag, hWF, hop, hL, hX, hx0]
    rfl
  · intro y
    obtain ⟨hU, -, hS, hI, hX, hL, -, hFlag, -⟩ :=
      fields_input q atkBit b n z ω (i := 1) (List.ofFn x)
        (pairEncode (pairEncode [] (pairEncode (List.ofFn (padFin ((pkOut 0).eval n)
          (pairFstD (List.ofFn x)))) (List.ofFn y))) []) j o hj
    have hWF : rWF (InteractiveHandler.input n z (List.ofFn ω) (List.ofFn (pkState q n j o))
        (1 : Fin 3)
        (List.ofFn x) (pairEncode (pairEncode [] (pairEncode (List.ofFn (padFin ((pkOut 0).eval n)
          (pairFstD (List.ofFn x)))) (List.ofFn y))) [])) = decWF n (List.ofFn x) := by
      rw [rWF, hU, hX, List.length_replicate, decWF_eq]
    have hY := rY_one _ _ _ hL
    have hans : List.ofFn (padFin ((pkDout 1).eval n)
        (true :: List.zipWith xor (pairSndD (List.ofFn x)) (List.ofFn y))) =
        true :: List.zipWith xor (pairSndD (List.ofFn x)) (List.ofFn y) :=
      GGMRed.ofFn_padFin_of_length (by
        rw [List.length_cons, List.length_zipWith, List.length_ofFn, hwf.2, hn, Nat.min_self,
          pkDout_one, PolyExpr.eval_add, PolyExpr.eval_var, PolyExpr.eval_const])
    rw [pkRun, hI, replicate_one, hFlag, hWF, hop, hL, log_ne_nil, if_neg Bool.false_ne_true,
      hans, hS, hX, hY]
    rfl

/-- **Closed decryption:** if the oracle is closed (CPA, or a record exists) or the query is not
well formed, the answer is `⊥` (all-`false`) and the state is kept. -/
theorem pkHandler_impl_dec_closed (x : Fin ((pkDin 1).eval n) → Bool) (j : ℕ)
    (o : Option (Fin (ctP.eval n) → Bool)) (hj : j ≤ q.eval n)
    (hcl : (atkBit && !o.isSome && decWF n (List.ofFn x)) = false) :
    (pkHandler q atkBit b).impl n z ω 1 x (pkState q n j o)
        = .pure (zeroBits _, pkState q n j o) := by
  refine impl_of_ret q atkBit b n z ω x _ _ _ ?_
  obtain ⟨hU, -, hS, hI, hX, -, -, hFlag, -⟩ :=
    fields_input q atkBit b n z ω (i := 1) (List.ofFn x) [] j o hj
  have hWF : rWF (InteractiveHandler.input n z (List.ofFn ω) (List.ofFn (pkState q n j o))
      (1 : Fin 3)
      (List.ofFn x) []) = decWF n (List.ofFn x) := by
    rw [rWF, hU, hX, List.length_replicate, decWF_eq]
  rw [pkRun, hI, replicate_one, hFlag, hWF, hcl, hU, hS, List.length_replicate, ofFn_zeroBits,
    pkDout_one]
  rfl

/-- **A recorded challenge is repeated:** from `pkState j (some c)`, a challenge is answered `c` and
the state is kept. -/
theorem pkHandler_impl_challenge_some (x : Fin ((pkDin 2).eval n) → Bool) (j : ℕ)
    (c : Fin (ctP.eval n) → Bool) (hj : j ≤ q.eval n) :
    (pkHandler q atkBit b).impl n z ω 2 x (pkState q n j (some c)) =
      .pure (padFin _ (List.ofFn c), pkState q n j (some c)) := by
  refine impl_of_ret q atkBit b n z ω x _ _ _ ?_
  obtain ⟨-, -, hS, hI, -, -, -, hFlag, hRec⟩ :=
    fields_input q atkBit b n z ω (i := 2) (List.ofFn x) [] j (some c) hj
  have hc : List.ofFn (padFin ((pkDout 2).eval n) (List.ofFn c)) = List.ofFn c :=
    GGMRed.ofFn_padFin_of_length (by rw [List.length_ofFn, pkDout_two])
  rw [pkRun, hI, replicate_two, hFlag, hRec, hS, hc]
  rfl

/-- **The first challenge with the next tape:** from `pkState j none` with `j < q(n)`, the
challenge `⟨m₀, m₁⟩` asks the outer oracle at the tape `r = T_j`, and its answer `y` gives the
ciphertext `c = ⟨r, m_b ⊕ y⟩`, recorded in the state `pkState (j + 1) (some c)`.

**Proof sketch.** As for `pkHandler_impl_enc`, with the selected half `m_b` (`rMsg`, `msgOf_eq`)
and the new record `recBits (some c)` written into the state (`rNew_fields`). -/
theorem pkHandler_impl_challenge_none (x : Fin ((pkDin 2).eval n) → Bool) (j : ℕ)
    (hj : j < q.eval n) :
    (pkHandler q atkBit b).impl n z ω 2 x (pkState q n j none) =
      .query 0 (padFin _ (List.ofFn (pkSeedTapes q atkBit b n ω ⟨j, hj⟩))) fun y =>
        .pure (padFin _ (ctOf (pkSeedTapes q atkBit b n ω ⟨j, hj⟩)
            (AdaptiveCPA.msgOf n b (List.ofFn x)) (padFin n (List.ofFn y))),
          pkState q n (j + 1) (some (padFin (ctP.eval n) (ctOf (pkSeedTapes q atkBit b n ω ⟨j, hj⟩)
            (AdaptiveCPA.msgOf n b (List.ofFn x)) (padFin n (List.ofFn y)))))) := by
  have hn : (pkOut 0).eval n = n := by rw [pkOut_eq, PolyExpr.eval_var]
  have hT : List.ofFn (padFin ((pkOut 0).eval n)
      (List.ofFn (pkSeedTapes q atkBit b n ω ⟨j, hj⟩))) =
      List.ofFn (pkSeedTapes q atkBit b n ω ⟨j, hj⟩) :=
    GGMRed.ofFn_padFin_of_length (by rw [List.length_ofFn, hn])
  have hmsg : (AdaptiveCPA.msgOf n b (List.ofFn x)).length = n := by
    have hx : (List.ofFn x).length = n + n := by
      rw [List.length_ofFn, pkDin_two, PolyExpr.eval_add, PolyExpr.eval_var]
    rw [AdaptiveCPA.msgOf_eq]
    cases b <;> simp [hx]
  refine impl_of_query q atkBit b n z ω x _ _ _ _ ?_ ?_
  · obtain ⟨-, -, -, hI, -, hL, -, hFlag, -⟩ :=
      fields_input q atkBit b n z ω (i := 2) (List.ofFn x) [] j none hj.le
    rw [pkRun, hI, replicate_two, hFlag, hL, hT,
      rNonce_fields q atkBit b n z ω (i := 2) _ _ j none hj]
    rfl
  · intro y
    obtain ⟨hU, -, -, hI, hX, hL, -, hFlag, -⟩ :=
      fields_input q atkBit b n z ω (i := 2) (List.ofFn x)
        (pairEncode (pairEncode [] (pairEncode (List.ofFn (padFin ((pkOut 0).eval n)
          (List.ofFn (pkSeedTapes q atkBit b n ω ⟨j, hj⟩)))) (List.ofFn y))) []) j none hj.le
    have hY := rY_one _ _ _ hL
    have hy : List.ofFn (padFin n (List.ofFn y)) = List.ofFn y :=
      GGMRed.ofFn_padFin_of_length (by rw [List.length_ofFn, hn])
    have hlen : (ctOf (pkSeedTapes q atkBit b n ω ⟨j, hj⟩) (AdaptiveCPA.msgOf n b (List.ofFn x))
        (padFin n (List.ofFn y))).length = ctP.eval n := by
      rw [length_ctOf _ hmsg, ctP_eval]
    have hct : List.ofFn (padFin ((pkDout 2).eval n) (ctOf (pkSeedTapes q atkBit b n ω ⟨j, hj⟩)
        (AdaptiveCPA.msgOf n b (List.ofFn x)) (padFin n (List.ofFn y)))) =
        ctOf (pkSeedTapes q atkBit b n ω ⟨j, hj⟩) (AdaptiveCPA.msgOf n b (List.ofFn x))
          (padFin n (List.ofFn y)) :=
      GGMRed.ofFn_padFin_of_length (by rw [hlen, pkDout_two])
    have hrec : true :: ctOf (pkSeedTapes q atkBit b n ω ⟨j, hj⟩)
        (AdaptiveCPA.msgOf n b (List.ofFn x)) (padFin n (List.ofFn y)) =
        recBits n (some (padFin (ctP.eval n) (ctOf (pkSeedTapes q atkBit b n ω ⟨j, hj⟩)
          (AdaptiveCPA.msgOf n b (List.ofFn x)) (padFin n (List.ofFn y))))) := by
      rw [recBits_some, GGMRed.ofFn_padFin_of_length hlen]
    have hMsg : rMsg b (InteractiveHandler.input n z (List.ofFn ω)
        (List.ofFn (pkState q n j none)) (2 : Fin 3) (List.ofFn x)
        (pairEncode (pairEncode [] (pairEncode (List.ofFn (padFin ((pkOut 0).eval n)
          (List.ofFn (pkSeedTapes q atkBit b n ω ⟨j, hj⟩)))) (List.ofFn y))) [])) =
        AdaptiveCPA.msgOf n b (List.ofFn x) := by
      rw [rMsg, hU, hX, List.length_replicate, AdaptiveCPA.msgOf_eq]
    have hctOf : ctOf (pkSeedTapes q atkBit b n ω ⟨j, hj⟩) (AdaptiveCPA.msgOf n b (List.ofFn x))
        (padFin n (List.ofFn y)) = pairEncode (List.ofFn (pkSeedTapes q atkBit b n ω ⟨j, hj⟩))
          (List.zipWith xor (AdaptiveCPA.msgOf n b (List.ofFn x)) (List.ofFn y)) := by
      rw [ctOf_eq, hy]
    rw [pkRun, hI, replicate_two]
    simp only [List.headD_cons, List.drop_succ_cons, List.drop_zero, if_true]
    rw [hFlag, hL, log_ne_nil]
    simp only [Option.isSome_none, Bool.false_eq_true, if_false]
    rw [hMsg, hct, rCt, rNonce_fields q atkBit b n z ω (i := 2) _ _ j none hj, hY, ← hctOf, hrec,
      rNew_fields q atkBit b n z ω (i := 2) _ _ j none _ hj.le]

end Answers

end TCSlib.Cryptography.Composability.PRFGame
