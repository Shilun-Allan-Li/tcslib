/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TCSlib.Cryptography.Encryption.PublicKey.OracleSecurity
import TCSlib.Cryptography.Games.Efficiency
import TCSlib.Cryptography.Asymptotic.OneWayLemmas
import TCSlib.Cryptography.Asymptotic.EnsemblesLemmas
import TCSlib.Cryptography.Asymptotic.CollectionsHelpers
import TCSlib.Cryptography.Asymptotic.CollectionsLemmas
import TCSlib.Cryptography.Pseudorandom.Functions.Asymptotic.GGM.Run
import TCSlib.Complexity.ClassNP.PolyTimePrefix

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The handler of the adaptive CPA reduction

The reduction from adaptive multi-challenge CPA security to single-challenge CPA security
[PS10, the single-to-many hybrid argument of p. 103, extended to adaptive challenges] runs the
adversary `A` once, on the public key `pk`. It answers decryption queries with `⊥`, the `j`-th
fresh challenge `⟨m₀, m₁⟩` with an encryption of `m₁` (`j < i⋆`) or `m₀` (`j > i⋆`) under its own
coins, forwards the `i⋆`-th fresh challenge to its own challenge oracle, and repeats the latest
ciphertext once the cap `κ = cap(n)` is reached. This file builds that reduction as a
`Games.InteractiveHandler` (`acHandler`), so that T2 (`Games.exists_interactiveHandlerMachine`)
makes it an oracle machine, and states its answers on the encoded states `acState j c` (the
count `j` of fresh challenges, the latest ciphertext `c` and the advised index `i⋆(n)`).

Its seed is `κ` encryption tapes, read as blocks of `ρ(n)` bits (`acTapes`). Its one outer call
per inner query is the forwarded challenge; its finalization asks nothing and outputs `A`'s bit.

## Main definitions

* `AdaptiveCPA.msgOf`: the message selected from a challenge query.
* `AdaptiveCPA.acDin`, `acDout`, `acStLen`: the oracle lengths and the state length.
* `AdaptiveCPA.acState`: the encoded state.
* `AdaptiveCPA.acTapes`: the seed as `κ` encryption tapes.
* `AdaptiveCPA.acHandler S cap ist`: the handler, with the advised index `ist n`.

## Main results

* `AdaptiveCPA.acHandler_impl_dec`, `_impl_full`, `_impl_eager`, `_impl_forward`: its answers.
* `AdaptiveCPA.acHandler_advInput`, `acHandler_finish`: the adversary's input and the output.

## References

* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010,
  Definition 171.5 and the single-to-many hybrid argument (book p. 103).
-/

namespace TCSlib.Cryptography.Composability.AdaptiveCPA

open Complexity Turing TCSlib.Cryptography TCSlib.Cryptography.Games

/-! ### Messages, lengths and states -/

/-- The message selected by the bit `β` from the challenge query `l = m₀ ‖ m₁` with `m`-bit
messages: `m₁ = l.drop m` for `β = true`, `m₀ = l.take m` for `β = false`. -/
def msgOf (m : ℕ) (β : Bool) (l : List Bool) : List Bool := if β then l.drop m else l.take m

/-- `msgOf m β l = if β then l.drop m else l.take m`. -/
theorem msgOf_eq (m : ℕ) (β : Bool) (l : List Bool) :
    msgOf m β l = if β then l.drop m else l.take m :=
  rfl

variable (S : FixedLengthPKScheme) (cap : PolyExpr) (ist : ℕ → ℕ)

/-- The query lengths of the two oracles: ciphertexts for `Dec`, two messages for `Challenge`. -/
def acDin : Fin 2 → PolyExpr
  | 0 => S.ctLen
  | 1 => S.msgLen.add S.msgLen

/-- `Dec` queries are ciphertexts: `acDin S 0 = S.ctLen`. -/
theorem acDin_zero : acDin S 0 = S.ctLen := rfl

/-- `Challenge` queries are two messages: `acDin S 1 = S.msgLen + S.msgLen`. -/
theorem acDin_one : acDin S 1 = S.msgLen.add S.msgLen := rfl

/-- The answer lengths: a validity flag and a message for `Dec`, a ciphertext for `Challenge`. -/
def acDout : Fin 2 → PolyExpr
  | 0 => S.msgLen.add (.const 1)
  | 1 => S.ctLen

/-- `Dec` answers a flag and a message: `acDout S 0 = S.msgLen + 1`. -/
theorem acDout_zero : acDout S 0 = S.msgLen.add (.const 1) := rfl

/-- `Challenge` answers a ciphertext: `acDout S 1 = S.ctLen`. -/
theorem acDout_one : acDout S 1 = S.ctLen := rfl

/-- The state length `4·cap + 4 + ctLen`, room for `⟨1^j, ⟨1^{i⋆}, c⟩⟩` with `j, i⋆ ≤ cap`. -/
def acStLen : PolyExpr := (((PolyExpr.const 4).mul cap).add (.const 4)).add S.ctLen

/-- `acStLen S cap = 4·cap + 4 + ctLen`. -/
theorem acStLen_eq : acStLen S cap = (((PolyExpr.const 4).mul cap).add (.const 4)).add S.ctLen :=
  rfl

/-- **The encoded state** after `j` fresh challenges with latest ciphertext `c`, for the advised
index `ist n`: the string `⟨1^j, ⟨1^{ist n}, c⟩⟩`, padded with `false` to the state length. -/
def acState (n j : ℕ) (c : Fin (S.ctLen.eval n) → Bool) : Fin ((acStLen S cap).eval n) → Bool :=
  padFin _ (pairEncode (List.replicate j true) (pairEncode (List.replicate (ist n) true)
    (List.ofFn c)))

/-- `acState S cap ist n j c = padFin _ ⟨1^j, ⟨1^{ist n}, c⟩⟩`. -/
theorem acState_eq (n j : ℕ) (c : Fin (S.ctLen.eval n) → Bool) :
    acState S cap ist n j c = padFin _ (pairEncode (List.replicate j true)
      (pairEncode (List.replicate (ist n) true) (List.ofFn c))) :=
  rfl

/-- **The seed as encryption tapes:** `cap(n) · ρ(n)` bits as `cap(n)` blocks of `ρ(n)` bits, each
read as coins of `Enc` (`FunFamily.blocks` and `NUPPT.coinsEquivPoly`). -/
def acTapes (n : ℕ) :
    (Fin ((cap.mul S.enc.coins).eval n) → Bool) ≃ (Fin (cap.eval n) → S.enc.Coins n) :=
  (FunFamily.blocks (cap.eval n) (S.enc.coins.eval n)).trans
    (Equiv.arrowCongr (Equiv.refl _) (NUPPT.coinsEquivPoly rfl n).symm)

/-- `acTapes S cap n ω j = (coinsEquivPoly rfl n).symm (FunFamily.blocks _ _ ω j)`. -/
theorem acTapes_apply (n : ℕ) (ω : Fin ((cap.mul S.enc.coins).eval n) → Bool)
    (j : Fin (cap.eval n)) :
    acTapes S cap n ω j =
      (NUPPT.coinsEquivPoly rfl n).symm (FunFamily.blocks (cap.eval n) (S.enc.coins.eval n) ω j) :=
  rfl

/-- **Tape `j` is the `j`-th block of the seed:**
`⟦acTapes S cap n ω j⟧ = (⟦ω⟧.drop (j·ρ(n))).take ρ(n)`.

**Proof sketch.** The coin equivalence keeps the string (`coinsEquivPoly_symm_ofFn`); position `k`
of block `j` is position `k + ρ·j` of `ω` (`FunFamily.blocks_apply`), which is position `k` of the
dropped and truncated list. -/
theorem ofFn_acTapes (n : ℕ) (ω : Fin ((cap.mul S.enc.coins).eval n) → Bool)
    (j : Fin (cap.eval n)) :
    List.ofFn (acTapes S cap n ω j) =
      ((List.ofFn ω).drop (j * S.enc.coins.eval n)).take (S.enc.coins.eval n) := by
  rw [acTapes, Equiv.trans_apply, Equiv.arrowCongr_apply, Function.comp_apply, Function.comp_apply,
    Equiv.refl_symm, Equiv.refl_apply, NUPPT.coinsEquivPoly_symm_ofFn]
  have hj := j.isLt
  have hle : (j : ℕ) * S.enc.coins.eval n + S.enc.coins.eval n ≤
      cap.eval n * S.enc.coins.eval n := by
    have := Nat.mul_le_mul_right (S.enc.coins.eval n) (Nat.succ_le_of_lt hj)
    rw [Nat.succ_mul] at this
    exact this
  refine List.ext_getElem ?_ fun k h₁ h₂ => ?_
  · simp only [List.length_ofFn, List.length_take, List.length_drop, PolyExpr.eval_mul]
    omega
  · rw [List.getElem_ofFn, List.getElem_take, List.getElem_drop, List.getElem_ofFn]
    refine (FunFamily.blocks_apply _ _ ω j ⟨k, _⟩).trans ?_
    congr 1
    refine Fin.ext ?_
    rw [finProdFinEquiv_apply_val]
    show k + S.enc.coins.eval n * j = j * S.enc.coins.eval n + k
    rw [Nat.mul_comm]
    omega

/-! ### Strings -/

/-- `⟦padFin k a⟧ = padL k a`, the first `k` bits of `a ++ 0^k` (`ofFn_padFin_eq_take`). -/
private theorem ofFn_padFin_eq_padL (k : ℕ) (a : List Bool) :
    List.ofFn (padFin k a) = EnsembleLemmas.padL k a := by
  rw [EnsembleLemmas.padL_eq, ofFn_padFin_eq_take]

/-- Appending to a pair appends to its second component. -/
private theorem pairEncode_append (u v t : List Bool) :
    pairEncode u v ++ t = pairEncode u (v ++ t) := by
  rw [pairEncode_eq, pairEncode_eq, List.append_assoc]

/-- The fields of an encoded state. -/
private theorem fields_acState (n j : ℕ) (c : Fin (S.ctLen.eval n) → Bool) (hj : j ≤ cap.eval n)
    (hi : ist n ≤ cap.eval n) :
    pairFstD (List.ofFn (acState S cap ist n j c)) = List.replicate j true ∧
      pairFstD (pairSndD (List.ofFn (acState S cap ist n j c))) =
        List.replicate (ist n) true ∧
      (pairSndD (pairSndD (List.ofFn (acState S cap ist n j c)))).take (S.ctLen.eval n) =
        List.ofFn c := by
  have hlen : (pairEncode (List.replicate j true) (pairEncode (List.replicate (ist n) true)
      (List.ofFn c))).length ≤ (acStLen S cap).eval n := by
    simp only [length_pairEncode, List.length_replicate, List.length_ofFn, acStLen_eq,
      PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const]
    omega
  rw [acState_eq, Collection.ofFn_padFin_of_le hlen, pairEncode_append, pairEncode_append]
  refine ⟨by rw [pairFstD_pairEncode], by rw [pairSndD_pairEncode, pairFstD_pairEncode], ?_⟩
  rw [pairSndD_pairEncode, pairSndD_pairEncode]
  exact List.take_left' List.length_ofFn

/-! ### The round function -/

/-- The parameter `1^n` of a round input `⟨⟨1^n, ⟨z, ω⟩⟩, ⟨s, ⟨⟨1^i, x⟩, L⟩⟩⟩`. -/
private def rU (w : List Bool) : List Bool := pairFstD (pairFstD w)
/-- The reduction input `z` (the public key). -/
private def rZ (w : List Bool) : List Bool := pairFstD (pairSndD (pairFstD w))
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
/-- The advised index `1^{i⋆}` of the state. -/
private def rIst (w : List Bool) : List Bool := pairFstD (pairSndD (rS w))
/-- The latest ciphertext of the state. -/
private def rLat (w : List Bool) : List Bool :=
  (pairSndD (pairSndD (rS w))).take (S.ctLen.eval (rU w).length)
/-- The outer answer recorded in the log `⟨⟨1, ⟨x, y⟩⟩, []⟩`. -/
private def rFwd (w : List Bool) : List Bool := pairSndD (pairSndD (pairFstD (rL w)))
/-- The new state `⟨1^{j+1}, ⟨1^{i⋆}, y⟩⟩`, padded. -/
private def rNew (w y : List Bool) : List Bool :=
  EnsembleLemmas.padL ((acStLen S cap).eval (rU w).length)
    (pairEncode (true :: rCnt w) (pairEncode (rIst w) y))
/-- The selected message: `m₁` below the advised index, `m₀` above it. -/
private def rMsg (w : List Bool) : List Bool :=
  if decide ((rCnt w).length < (rIst w).length) then (rX w).drop (S.msgLen.eval (rU w).length)
  else (rX w).take (S.msgLen.eval (rU w).length)
/-- Tape `j` of the seed. -/
private def rTape (w : List Bool) : List Bool :=
  ((rW w).drop ((rCnt w).length * S.enc.coins.eval (rU w).length)).take
    (S.enc.coins.eval (rU w).length)
/-- The handler's own encryption of the selected message with tape `j`, padded. -/
private def rEnc (w : List Bool) : List Bool :=
  EnsembleLemmas.padL (S.ctLen.eval (rU w).length)
    (S.enc.output (pairEncode (pairEncode (pairEncode (rU w) (pairEncode (rZ w) (rMsg S w))) [])
      (rTape S w)))

/-- **One round of the handler.** A decryption query is answered `0^{m+1}`, keeping the state. A
challenge at the cap repeats the latest ciphertext. The fresh challenge `j = i⋆` is forwarded
to the outer challenge oracle and answered with the outer answer. Any other fresh challenge is
answered with the handler's own encryption. A fresh challenge records its answer and counts. -/
private def acRun (w : List Bool) : List Bool :=
  if (rI w).headD false then
    if decide (cap.eval (rU w).length ≤ (rCnt w).length) then pairEncode [true] (rLat S w ++ rS w)
    else if decide ((rCnt w).length = (rIst w).length) then
      if decide (rL w = []) then pairEncode [false] (pairEncode [true] (rX w))
      else pairEncode [true] (rFwd w ++ rNew S cap w (rFwd w))
    else pairEncode [true] (rEnc S w ++ rNew S cap w (rEnc S w))
  else pairEncode [true] (List.replicate ((S.msgLen.add (.const 1)).eval (rU w).length) false ++
    rS w)

/-- The round function is polynomial-time. -/
private theorem polyTimeComputable_acRun : PolyTimeComputable (acRun S cap) := by
  have hF := polyTimeComputable_pairFstD
  have hD := polyTimeComputable_pairSndD
  have hU : PolyTimeComputable rU := hF.comp hF
  have hZ : PolyTimeComputable rZ := hF.comp (hD.comp hF)
  have hW : PolyTimeComputable rW := hD.comp (hD.comp hF)
  have hS : PolyTimeComputable rS := hF.comp hD
  have hI : PolyTimeComputable rI := hF.comp (hF.comp (hD.comp hD))
  have hX : PolyTimeComputable rX := hD.comp (hF.comp (hD.comp hD))
  have hL : PolyTimeComputable rL := hD.comp (hD.comp hD)
  have hCnt : PolyTimeComputable rCnt := hF.comp hS
  have hIst : PolyTimeComputable rIst := hF.comp (hD.comp hS)
  have hLat : PolyTimeComputable (rLat S) :=
    ((polyTimeComputable_pairTakePoly S.ctLen).comp (hU.pairEncode (hD.comp (hD.comp hS)))).congr
      fun w => by simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]; rfl
  have hFwd : PolyTimeComputable rFwd := hD.comp (hD.comp (hF.comp hL))
  have hNew : ∀ {y : List Bool → List Bool}, PolyTimeComputable y →
      PolyTimeComputable fun w => rNew S cap w (y w) := fun hy =>
    EnsembleLemmas.polyTimeComputable_padL (acStLen S cap) hU
      (((polyTimeComputable_const [true]).append hCnt).pairEncode (hIst.pairEncode hy))
  have hLt : PolyTimeComputable fun w => [decide ((rCnt w).length < (rIst w).length)] :=
    (polyTimeComputable_not (polyTimeComputable_lenLe.comp (hCnt.pairEncode hIst))).congr
      fun w => by
        simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode, List.cons.injEq,
          and_true]
        by_cases h : (rCnt w).length < (rIst w).length
        · rw [decide_eq_true h, decide_eq_false (by omega)]
          rfl
        · rw [decide_eq_false h, decide_eq_true (by omega)]
          rfl
  have hMsg : PolyTimeComputable (rMsg S) :=
    polyTimeComputable_ite hLt
      (((polyTimeComputable_pairDropPoly S.msgLen).comp (hU.pairEncode hX)).congr fun w => by
        simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode])
      (((polyTimeComputable_pairTakePoly S.msgLen).comp (hU.pairEncode hX)).congr fun w => by
        simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode])
  have hOff : PolyTimeComputable fun w =>
      List.replicate ((rCnt w).length * S.enc.coins.eval (rU w).length) true :=
    (OneWay.polyTimeComputable_unaryMulPair.comp
      (hCnt.pairEncode ((polyTimeComputable_unaryPoly S.enc.coins).comp hU))).congr fun w => by
        simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode,
          List.length_replicate]
  have hDrop : PolyTimeComputable fun w =>
      (rW w).drop ((rCnt w).length * S.enc.coins.eval (rU w).length) :=
    (polyTimeComputable_dropPrefixByLength.comp (hOff.pairEncode hW)).congr fun w => by
      simp only [Function.comp_apply, PrefixByLength.drop_def, pairFstD_pairEncode,
        pairSndD_pairEncode, List.length_replicate]
  have hTape : PolyTimeComputable (rTape S) :=
    ((polyTimeComputable_pairTakePoly S.enc.coins).comp (hU.pairEncode hDrop)).congr fun w => by
      simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode]; rfl
  have hEnc : PolyTimeComputable (rEnc S) :=
    EnsembleLemmas.polyTimeComputable_padL S.ctLen hU (S.enc.polyTimeComputable_output.comp
      (((hU.pairEncode (hZ.pairEncode hMsg)).pairEncode (polyTimeComputable_const [])).pairEncode
        hTape))
  have hRet : ∀ {f : List Bool → List Bool}, PolyTimeComputable f →
      PolyTimeComputable fun w => pairEncode [true] (f w) := fun hf =>
    (polyTimeComputable_const [true]).pairEncode hf
  have cFull : PolyTimeComputable fun w =>
      [decide (cap.eval (rU w).length ≤ (rCnt w).length)] :=
    (polyTimeComputable_lenLe.comp (hCnt.pairEncode
      ((polyTimeComputable_unaryPoly cap).comp hU))).congr fun w => by
        simp only [Function.comp_apply, pairFstD_pairEncode, pairSndD_pairEncode,
          List.length_replicate]
  have cEq : PolyTimeComputable fun w => [decide ((rCnt w).length = (rIst w).length)] :=
    EffFill.lenEq_poly hCnt hIst
  have cNil : PolyTimeComputable fun w => [decide (rL w = [])] := polyTimeComputable_isNil.comp hL
  have hZeros : PolyTimeComputable fun w =>
      List.replicate ((S.msgLen.add (.const 1)).eval (rU w).length) false :=
    EnsembleLemmas.polyTimeComputable_zeros _ hU
  exact polyTimeComputable_ite (polyTimeComputable_headD.comp hI)
    (polyTimeComputable_ite cFull (hRet (hLat.append hS))
      (polyTimeComputable_ite cEq
        (polyTimeComputable_ite cNil
          ((polyTimeComputable_const [false]).pairEncode
            ((polyTimeComputable_const [true]).pairEncode hX))
          (hRet (hFwd.append (hNew hFwd))))
        (hRet (hEnc.append (hNew hEnc)))))
    (hRet (hZeros.append hS))

/-- The finalization's round: output `A`'s bit, `⟨[true], a⟩` on `⟨ctx, ⟨s, ⟨a, L⟩⟩⟩`. -/
private def acFin (w : List Bool) : List Bool :=
  pairEncode [true] (pairFstD (pairSndD (pairSndD w)))

/-- The finalization's round is polynomial-time. -/
private theorem polyTimeComputable_acFin : PolyTimeComputable acFin :=
  (polyTimeComputable_const [true]).pairEncode
    (polyTimeComputable_pairFstD.comp
      (polyTimeComputable_pairSndD.comp polyTimeComputable_pairSndD))

/-! ### The handler -/

/-- **The handler of the adaptive CPA reduction** for the scheme `S`, the cap `cap` and the advised
index `ist`: state `acState j c` (initially `j = 0`, `c = 0`), seed `cap · ρ` bits (the tapes
`acTapes`), one outer call per inner query, the adversary run on the reduction input, and the
finalization outputting the adversary's bit without outer queries. -/
def acHandler : InteractiveHandler 2 (acDin S) (acDout S) 2 (acDin S) (acDout S) where
  stateLen := acStLen S cap
  seedLen := cap.mul S.enc.coins
  perCall := .const 1
  init n := acState S cap ist n 0 (zeroBits _)
  run := acRun S cap
  poly := polyTimeComputable_acRun S cap
  advIn ctx := pairFstD (pairSndD ctx)
  advIn_poly := polyTimeComputable_pairFstD.comp polyTimeComputable_pairSndD
  outLen := .const 1
  finCall := .const 0
  finRun := acFin
  finRun_poly := polyTimeComputable_acFin

attribute [simps (config := { isSimp := false }) stateLen seedLen perCall init advIn outLen finCall]
  acHandler

/-- The handler's state `acState S cap ist n j c`, at the handler's state type. -/
def acHState (n j : ℕ) (c : Fin (S.ctLen.eval n) → Bool) :
    Fin ((acHandler S cap ist).stateLen.eval n) → Bool :=
  acState S cap ist n j c

/-- `acHState S cap ist n j c = acState S cap ist n j c`. -/
theorem acHState_eq (n j : ℕ) (c : Fin (S.ctLen.eval n) → Bool) :
    acHState S cap ist n j c = acState S cap ist n j c :=
  rfl

/-- The handler starts from no fresh challenge and the all-`false` ciphertext:
`(acHandler S cap ist).init n = acHState S cap ist n 0 0`. -/
theorem acHandler_init_eq (n : ℕ) :
    (acHandler S cap ist).init n = acHState S cap ist n 0 (zeroBits _) :=
  rfl

/-- The handler's seed as encryption tapes (`acTapes`). -/
def acSeedTapes (n : ℕ) :
    (Fin ((acHandler S cap ist).seedLen.eval n) → Bool) ≃ (Fin (cap.eval n) → S.enc.Coins n) :=
  acTapes S cap n

/-- `acSeedTapes S cap ist n = acTapes S cap n`. -/
theorem acSeedTapes_eq (n : ℕ) : acSeedTapes S cap ist n = acTapes S cap n :=
  rfl

/-- Tape `j` of the handler's seed is its `j`-th block (`ofFn_acTapes`). -/
private theorem ofFn_acSeedTapes (n : ℕ) (ω : Fin ((acHandler S cap ist).seedLen.eval n) → Bool)
    (j : Fin (cap.eval n)) :
    List.ofFn (acSeedTapes S cap ist n ω j) =
      ((List.ofFn ω).drop (j * S.enc.coins.eval n)).take (S.enc.coins.eval n) :=
  ofFn_acTapes S cap n ω j

/-- The adversary runs on the reduction input: `(acHandler S cap ist).advInput n z ω = z`. -/
theorem acHandler_advInput (n : ℕ) (z : List Bool)
    (ω : Fin ((acHandler S cap ist).seedLen.eval n) → Bool) :
    (acHandler S cap ist).advInput n z ω = z := by
  rw [InteractiveHandler.advInput_eq, acHandler_advIn, seedIn_eq, pairSndD_pairEncode,
    pairFstD_pairEncode]

/-- The finalization outputs the adversary's bit and asks nothing:
`(acHandler S cap ist).finish n z ω s a = pure (padFin _ ⟦a⟧)`, the bit `a` read at the output
width. -/
theorem acHandler_finish (n : ℕ) (z : List Bool)
    (ω : Fin ((acHandler S cap ist).seedLen.eval n) → Bool)
    (s : Fin ((acHandler S cap ist).stateLen.eval n) → Bool)
    (a : Fin ((PolyExpr.const 1).eval n) → Bool) :
    (acHandler S cap ist).finish n z ω s a =
      .pure (padFin ((acHandler S cap ist).outLen.eval n) (List.ofFn a)) := by
  rw [InteractiveHandler.finish_eq]
  refine buildComp_zero_of_ret ?_
  show decodeBitMove _ _ _ (acFin _) = _
  rw [acFin, InteractiveHandler.finInput_eq, pairSndD_pairEncode, pairSndD_pairEncode,
    pairFstD_pairEncode]
  have hw : List.ofFn (padFin ((acHandler S cap ist).outLen.eval n) (List.ofFn a)) = List.ofFn a :=
    GGMRed.ofFn_padFin_of_length (by rw [List.length_ofFn, acHandler_outLen])
  exact (congrArg (fun w => decodeBitMove _ _ _ (pairEncode [true] w)) hw).symm.trans
    (decodeBitMove_ret _ _ _ _)

/-! ### Answers of the handler -/

section Answers

variable (n : ℕ) (z : List Bool) (ω : Fin ((acHandler S cap ist).seedLen.eval n) → Bool)

/-- A call whose first round returns `y ‖ s'` is answered `y` with new state `s'`. -/
private theorem impl_of_ret {i : Fin 2} (x : Fin ((acDin S i).eval n) → Bool)
    (s : Fin ((acStLen S cap).eval n) → Bool) (y : Fin ((acDout S i).eval n) → Bool)
    (s' : Fin ((acStLen S cap).eval n) → Bool)
    (h : acRun S cap (InteractiveHandler.input n z (List.ofFn ω) (List.ofFn s) i (List.ofFn x) []) =
      pairEncode [true] (List.ofFn y ++ List.ofFn s')) :
    (acHandler S cap ist).impl n z ω i x s = .pure (y, s') := by
  rw [InteractiveHandler.impl_apply, InteractiveHandler.call_eq, acHandler_perCall,
    PolyExpr.eval_const]
  rw [buildComp_succ_of_ret (a := Fin.append y s') (by
    show decodeBitMove _ _ _ (acRun S cap _) = _
    rw [MachineCodec.encodeLog_nil, h, ← List.ofFn_fin_append]
    exact decodeBitMove_ret _ _ _ _), OracleComp.pure_bind]
  congr 2
  · funext j
    exact Fin.append_left y s' j
  · funext j
    exact Fin.append_right y s' j

/-- The index word of a challenge query is `[true]`. -/
private theorem replicate_one : List.replicate ((1 : Fin 2) : ℕ) true = [true] := rfl

/-- The round input of a call, field by field. -/
private theorem fields_input {i : Fin 2} (x : List Bool) (L : List Bool) (j : ℕ)
    (c : Fin (S.ctLen.eval n) → Bool) (hj : j ≤ cap.eval n) (hi : ist n ≤ cap.eval n) :
    let w := InteractiveHandler.input n z (List.ofFn ω) (List.ofFn (acState S cap ist n j c)) i x L
    rU w = List.replicate n true ∧ rZ w = z ∧ rW w = List.ofFn ω ∧
      rS w = List.ofFn (acState S cap ist n j c) ∧ rI w = List.replicate i true ∧ rX w = x ∧
      rL w = L ∧ rCnt w = List.replicate j true ∧ rIst w = List.replicate (ist n) true ∧
      rLat S w = List.ofFn c := by
  obtain ⟨h₁, h₂, h₃⟩ := fields_acState S cap ist n j c hj hi
  simp only [InteractiveHandler.input_eq, rU, rZ, rW, rS, rI, rX, rL, rCnt, rIst, rLat,
    pairFstD_pairEncode, pairSndD_pairEncode, List.length_replicate, h₁, h₂, h₃, and_self]

/-- **Decryption is refused:** `(acHandler S cap ist).impl n z ω 0 x s = pure (0, s)`. -/
theorem acHandler_impl_dec (x : Fin ((acDin S 0).eval n) → Bool)
    (s : Fin ((acHandler S cap ist).stateLen.eval n) → Bool) :
    (acHandler S cap ist).impl n z ω 0 x s = .pure (zeroBits _, s) := by
  refine impl_of_ret S cap ist n z ω x s _ _ ?_
  have hI : rI (InteractiveHandler.input n z (List.ofFn ω) (List.ofFn s) (0 : Fin 2) (List.ofFn x)
      []) =
      [] := by
    simp only [InteractiveHandler.input_eq, rI, pairFstD_pairEncode, pairSndD_pairEncode]
    rfl
  have hU : rU (InteractiveHandler.input n z (List.ofFn ω) (List.ofFn s) (0 : Fin 2) (List.ofFn x)
      []) =
      List.replicate n true := by
    simp only [InteractiveHandler.input_eq, rU, pairFstD_pairEncode]
  have hS : rS (InteractiveHandler.input n z (List.ofFn ω) (List.ofFn s) (0 : Fin 2) (List.ofFn x)
      []) =
      List.ofFn s := by
    simp only [InteractiveHandler.input_eq, rS, pairFstD_pairEncode, pairSndD_pairEncode]
  rw [acRun, hI, List.headD_nil, if_neg Bool.false_ne_true, hU, hS, List.length_replicate,
    ofFn_zeroBits, acDout_zero]

/-- **At the cap, the latest ciphertext is repeated:** from the state `acState κ c` with
`κ = cap(n)`, a challenge is answered `c` and the state is kept. -/
theorem acHandler_impl_full (x : Fin ((acDin S 1).eval n) → Bool)
    (c : Fin (S.ctLen.eval n) → Bool) (hi : ist n ≤ cap.eval n) :
    (acHandler S cap ist).impl n z ω 1 x (acHState S cap ist n (cap.eval n) c) =
      .pure (padFin ((acDout S 1).eval n) (List.ofFn c), acHState S cap ist n (cap.eval n) c) := by
  rw [acHState_eq]
  refine impl_of_ret S cap ist n z ω x _ _ _ ?_
  obtain ⟨hU, -, -, hS, hI, -, -, hCnt, -, hLat⟩ :=
    fields_input S cap ist n z ω (i := 1) (List.ofFn x) [] (cap.eval n) c le_rfl hi
  have hh : ([true].headD false = true) := rfl
  have hc : decide (cap.eval n ≤ cap.eval n) = true := decide_eq_true le_rfl
  rw [acRun, hI, replicate_one, hU, hCnt, hS, hLat, List.length_replicate, List.length_replicate,
    if_pos hh, if_pos hc, GGMRed.ofFn_padFin_of_length (List.length_ofFn)]

/-- **A fresh challenge other than the advised one is encrypted by the handler:** from the state
`acState j c` with `j < cap(n)` and `j ≠ i⋆(n)`, the challenge `x` is answered with
`c' = padFin (Enc_z(m_{[j < i⋆]}); tape j)`, recorded in the state `acState (j + 1) c'`. -/
theorem acHandler_impl_eager (x : Fin ((acDin S 1).eval n) → Bool) (j : ℕ)
    (c : Fin (S.ctLen.eval n) → Bool) (hj : j < cap.eval n) (hne : j ≠ ist n)
    (hi : ist n ≤ cap.eval n) :
    (acHandler S cap ist).impl n z ω 1 x (acHState S cap ist n j c) =
      .pure (padFin ((acDout S 1).eval n) (List.ofFn (padFin (S.ctLen.eval n) (S.enc.runAt n
          (pairEncode z (msgOf (S.msgLen.eval n) (decide (j < ist n)) (List.ofFn x)))
          (acSeedTapes S cap ist n ω ⟨j, hj⟩)))),
        acHState S cap ist n (j + 1) (padFin (S.ctLen.eval n) (S.enc.runAt n
          (pairEncode z (msgOf (S.msgLen.eval n) (decide (j < ist n)) (List.ofFn x)))
          (acSeedTapes S cap ist n ω ⟨j, hj⟩)))) := by
  rw [acHState_eq, acHState_eq]
  obtain ⟨c', hc'⟩ : ∃ c' : Fin (S.ctLen.eval n) → Bool, c' = padFin (S.ctLen.eval n)
      (S.enc.runAt n (pairEncode z (msgOf (S.msgLen.eval n) (decide (j < ist n)) (List.ofFn x)))
        (acSeedTapes S cap ist n ω ⟨j, hj⟩)) := ⟨_, rfl⟩
  rw [← hc']
  refine impl_of_ret S cap ist n z ω x _ _ _ ?_
  obtain ⟨hU, hZ, hW, hS, hI, hX, -, hCnt, hIst, -⟩ :=
    fields_input S cap ist n z ω (i := 1) (List.ofFn x) [] j c hj.le hi
  have hEnc : rEnc S (InteractiveHandler.input n z (List.ofFn ω)
      (List.ofFn (acState S cap ist n j c)) (1 : Fin 2) (List.ofFn x) []) = List.ofFn c' := by
    rw [hc', ofFn_padFin_eq_padL, rEnc, hU, List.length_replicate, NUPPT.Uniform.runAt_eq
      S.enc_uniform, NUPPT.advInput_eq, ofFn_acSeedTapes, rTape, rMsg, hZ, hW, hCnt, hIst, hU, hX,
      List.length_replicate, List.length_replicate, List.length_replicate, msgOf_eq]
  have hNew : rNew S cap (InteractiveHandler.input n z (List.ofFn ω)
      (List.ofFn (acState S cap ist n j c)) (1 : Fin 2) (List.ofFn x) []) (List.ofFn c') =
      List.ofFn (acState S cap ist n (j + 1) c') := by
    rw [rNew, hU, hCnt, hIst, List.length_replicate, acState_eq, ofFn_padFin_eq_padL,
      List.replicate_succ]
  have hh : ([true].headD false = true) := rfl
  have hc1 : ¬ (decide (cap.eval n ≤ j) = true) := by rw [decide_eq_true_eq]; omega
  have hc2 : ¬ (decide (j = ist n) = true) := by rw [decide_eq_true_eq]; exact hne
  rw [acRun, hI, replicate_one, hU, hCnt, hIst, hEnc, hNew, List.length_replicate,
    List.length_replicate, List.length_replicate, if_pos hh, if_neg hc1, if_neg hc2,
    GGMRed.ofFn_padFin_of_length (List.length_ofFn)]

/-- **The advised fresh challenge is forwarded:** from the state `acState j c` with
`j = i⋆(n) < cap(n)`, the challenge `x` is asked to the outer challenge oracle, and its answer `y`
is returned and recorded in the state `acState (j + 1) y`. -/
theorem acHandler_impl_forward (x : Fin ((acDin S 1).eval n) → Bool) (j : ℕ)
    (c : Fin (S.ctLen.eval n) → Bool) (hj : j < cap.eval n) (heq : j = ist n) :
    (acHandler S cap ist).impl n z ω 1 x (acHState S cap ist n j c) =
      .query 1 x fun y =>
        .pure (y, acHState S cap ist n (j + 1) (padFin (S.ctLen.eval n) (List.ofFn y))) := by
  simp only [acHState_eq]
  have hi : ist n ≤ cap.eval n := heq ▸ hj.le
  have hlen : ∀ m : ℕ, (List.replicate m true).length = m := fun m => List.length_replicate
  rw [InteractiveHandler.impl_apply, InteractiveHandler.call_eq, acHandler_perCall,
    PolyExpr.eval_const]
  rw [buildComp_succ_of_query (i := 1) (x := x) (by
    show decodeBitMove _ _ _ (acRun S cap _) = _
    obtain ⟨hU, -, -, -, hI, hX, hL, hCnt, hIst, -⟩ :=
      fields_input S cap ist n z ω (i := 1) (List.ofFn x)
        ((bitCodec (fun j => (acDin S j).eval n) (fun j => (acDout S j).eval n) 0).encodeLog [])
        j c hj.le hi
    have hh : ([true].headD false = true) := rfl
    have hc1 : ¬ (decide (cap.eval n ≤ j) = true) := by rw [decide_eq_true_eq]; omega
    have hc2 : decide (j = ist n) = true := decide_eq_true heq
    have hc3 : decide (([] : List Bool) = []) = true := decide_eq_true rfl
    rw [acRun, hI, replicate_one, hU, hCnt, hIst, hL, hX, MachineCodec.encodeLog_nil, hlen, hlen,
      hlen, if_pos hh, if_neg hc1, if_pos hc2, if_pos hc3, ← replicate_one]
    exact decodeBitMove_query (fun j => (acDin S j).eval n) (fun j => (acDout S j).eval n) _ 1 x),
    OracleComp.query_bind]
  congr 1
  funext y
  obtain ⟨s', hs'⟩ : ∃ s' : Fin ((acStLen S cap).eval n) → Bool,
      s' = acState S cap ist n (j + 1) (padFin (S.ctLen.eval n) (List.ofFn y)) := ⟨_, rfl⟩
  rw [← hs']
  rw [buildComp_zero_of_ret (a := Fin.append y s') (by
    show decodeBitMove _ _ _ (acRun S cap _) = _
    obtain ⟨hU, -, -, -, hI, -, hL, hCnt, hIst, -⟩ :=
      fields_input S cap ist n z ω (i := 1) (List.ofFn x)
        ((bitCodec (fun j => (acDin S j).eval n) (fun j => (acDout S j).eval n) 0).encodeLog
          ([] ++ [⟨1, x, y⟩])) j c hj.le hi
    have hlog : (bitCodec (fun j => (acDin S j).eval n) (fun j => (acDout S j).eval n) 0).encodeLog
        ([] ++ [⟨1, x, y⟩]) = pairEncode (pairEncode [true] (pairEncode (List.ofFn x)
          (List.ofFn y))) [] := by
      rw [List.nil_append, MachineCodec.encodeLog_cons, MachineCodec.encodeLog_nil,
        bitCodec_encodeEntry]
      rfl
    have hNew : rNew S cap (InteractiveHandler.input n z (List.ofFn ω)
        (List.ofFn (acState S cap ist n j c)) (1 : Fin 2) (List.ofFn x)
        ((bitCodec (fun j => (acDin S j).eval n) (fun j => (acDout S j).eval n) 0).encodeLog
          ([] ++ [⟨1, x, y⟩]))) (List.ofFn y) = List.ofFn s' := by
      rw [rNew, hU, hCnt, hIst, List.length_replicate, hs', acState_eq, ofFn_padFin_eq_padL,
        List.replicate_succ, GGMRed.ofFn_padFin_of_length (List.length_ofFn)]
    have hFwd : rFwd (InteractiveHandler.input n z (List.ofFn ω)
        (List.ofFn (acState S cap ist n j c)) (1 : Fin 2) (List.ofFn x)
        ((bitCodec (fun j => (acDin S j).eval n) (fun j => (acDout S j).eval n) 0).encodeLog
          ([] ++ [⟨1, x, y⟩]))) = List.ofFn y := by
      rw [rFwd, hL, hlog, pairFstD_pairEncode, pairSndD_pairEncode, pairSndD_pairEncode]
    have hh : ([true].headD false = true) := rfl
    have hc1 : ¬ (decide (cap.eval n ≤ j) = true) := by rw [decide_eq_true_eq]; omega
    have hc2 : decide (j = ist n) = true := decide_eq_true heq
    have hc3 : ¬ (decide (pairEncode (pairEncode [true] (pairEncode (List.ofFn x) (List.ofFn y)))
        [] = []) = true) := by
      rw [decide_eq_true_eq]
      exact pairEncode_ne_nil _ _
    rw [acRun, hI, replicate_one, hU, hCnt, hIst, hFwd, hNew, hL, hlog, hlen, hlen, hlen,
      if_pos hh, if_neg hc1, if_pos hc2, if_neg hc3, ← List.ofFn_fin_append]
    exact decodeBitMove_ret _ _ _ _)]
  rw [OracleComp.pure_bind]
  congr 2
  · funext k
    exact Fin.append_left y s' k
  · funext k
    exact Fin.append_right y s' k

end Answers

end TCSlib.Cryptography.Composability.AdaptiveCPA
