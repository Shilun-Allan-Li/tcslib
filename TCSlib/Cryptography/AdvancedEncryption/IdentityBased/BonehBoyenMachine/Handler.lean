/-
Copyright (c) 2026 TCSlib contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TCSlib contributors
-/
import TCSlib.Cryptography.AdvancedEncryption.IdentityBased.BonehBoyenMachine.Words
import TCSlib.Cryptography.Games.Efficiency
import TCSlib.Cryptography.Pairing.Assumptions
import TCSlib.Cryptography.Pairing.Operations

set_option maxHeartbeats 0
set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The BB1 simulator as a polynomial-time handler

Helper module of `AdvancedEncryption/IdentityBased/BonehBoyenMachine.lean` (step 3 of
[BB04, proof of Theorem 4.1] at depth `ℓ = 1`): the paper's algorithm `B` answering the
adversary's `Init`, `KeyGen` and `Challenge` queries, as a polynomial-time handler
(`Games.PolyHandler`) of the handler theorem T1 (`Games.exists_handlerMachine`). It works on
the encodings only: group operations by the contract `Pairing.BilinearGen.Ops`, exponent
arithmetic modulo `p` by the arithmetic bundle `Candidates.ArithmeticFP`, and each exponent
`α_1`, `r` drawn from the next block of `n · n` seed bits by the rejection sampler of
`BonehBoyenMachine/Draws.lean`. The string functions it is assembled from (readers of the round
input, arithmetic modulo `p`, the group operations, the drawn exponent) are those of
`BonehBoyenMachine/Words.lean`.

**The run.** The reduction input is the Decision BDH string `⟨d, ⟨g, ⟨X, ⟨Y, ⟨Z, T⟩⟩⟩⟩⟩` and the
seed `ω` holds `q(κ)` blocks of `n · n` bits. The state is `⟨1^j, ⟨o_1, o_2⟩⟩` padded to a fixed
length: `j` queries answered so far, `o_1 = ⟨ID*, α_1⟩` (the committed identity and `α_1` as a
`(wG(κ) + 1)`-bit numeral) or empty, and `o_2 = 1 ‖ C` (the recorded challenge) or empty. The
`j`-th query reads its exponent from block `j`. Negation and differences of residues are
computed with truncated subtraction and division with remainder, and inverses with the extended
Euclidean algorithm, whose inverse of `0` is `0`, as in `Z_p`.

**Its meaning.** On the encoding of a state of the simulator, one query to the handler is one
query to `drawStep` with the exponent read from the seed (`handler_impl_stEnc`), so the whole
run is the run of `drawStep` with exponents read from a tape, through the encoding of the states
(`simulate_handler`).

## Main definitions

* `BB1Machine.handler` — the handler.
* `BB1Machine.seedBlocks` — the seed as `q(κ)` blocks of `n · n` bits.

## Main results

* `BB1Machine.handler_advInput`, `BB1Machine.handler_result` — the adversary's input and the
  reduction's output.
* `BB1Machine.seedBlocks_window` — block `j` of the seed is its `j`-th window of `n · n` bits.
* `BB1Machine.simulate_handler` — the handler's run is the run of `drawStep` with exponents
  drawn from the seed blocks.

## References

* [BB04] D. Boneh, X. Boyen, *Efficient Selective-ID Secure Identity Based Encryption Without
  Random Oracles*, full version, Cryptology ePrint Archive, Report 2004/172, December 2004
  (extended abstract: EUROCRYPT 2004, LNCS 3027, pp. 223–238). §4.2 (pp. 6–8): the algorithm
  `B` in the proof of Theorem 4.1.
* [PS10] R. Pass, a. shelat, *A Course in Cryptography*, lecture notes, 3rd ed., January 2010.
  (Algorithm 43.2, the extended Euclidean algorithm; Theorem 52.3, sampling `Z_q`.)
-/

namespace TCSlib.Cryptography.AdvancedEncryption.IdentityBased

open Complexity Turing TCSlib.Cryptography.Games TCSlib.Cryptography.Pairing
  TCSlib.Cryptography.Composability TCSlib.Cryptography.NumberTheory
  TCSlib.Cryptography.Candidates

namespace BB1Machine

noncomputable section

variable (G : BilinearGen) (ℓ : PolyExpr) (O : G.Ops) (b : Bool) (q : PolyExpr)

/-! ### Lengths -/

/-- The state length `2q + 4ℓ + 4wG + wT + 11`, room for `⟨1^j, ⟨⟨ID*, α_1⟩, 1 ‖ C⟩⟩`, `j ≤ q`. -/
private def stLen : PolyExpr :=
  ((((q.mul (.const 2)).add (ℓ.mul (.const 4))).add (G.wG.mul (.const 4))).add G.wT).add
    (.const 11)

/-! ### The answers -/

/-- `h = X^{(−t).val} · g^{α}` for the identity word `t` and the numeral `a` of `α`. -/
private def hS (w t a : List Bool) : List Bool :=
  mulGS G O w (powGS G O w (zX w) (negS G O w t)) (powGS G O w (zG w) a)

/-- The committed identity for `Init`: the recorded one, or the query. -/
private def tSel (w : List Bool) : List Bool := if sCom w then kT w else rX w
/-- The committed exponent for `Init`: the recorded one, or the drawn one. -/
private def aSel (w : List Bool) : List Bool := if sCom w then kA w else uS G O w

/-- `Init`'s answer `d ‖ g ‖ X ‖ Y ‖ h`. -/
private def ans0 (w : List Bool) : List Bool :=
  zD w ++ zG w ++ zX w ++ zY w ++ hS G O w (tSel w) (aSel G O w)

/-- Whether `KeyGen` answers a key: committed and `ID ≠ ID*`. -/
private def keyOk (w : List Bool) : Bool := sCom w && !decide (rX w = kT w)
/-- The residue of `ID − ID*`. -/
private def diffS (w : List Bool) : List Bool :=
  addS G O w (modS G O w (rX w)) (negS G O w (kT w))
/-- The residue of `1/(ID − ID*)`. -/
private def invD (w : List Bool) : List Bool := invS G O w (diffS G O w)
/-- `d_0 = Y^{(−α_1/(ID − ID*)).val} · (X^{ID.val} · h)^{r.val}`. -/
private def d0S (w : List Bool) : List Bool :=
  mulGS G O w (powGS G O w (zY w) (mulS G O w (negS G O w (kA w)) (invD G O w)))
    (powGS G O w (mulGS G O w (powGS G O w (zX w) (modS G O w (rX w)))
      (hS G O w (kT w) (kA w))) (uS G O w))
/-- `d_1 = Y^{(−1/(ID − ID*)).val} · g^{r.val}`. -/
private def d1S (w : List Bool) : List Bool :=
  mulGS G O w (powGS G O w (zY w) (negS G O w (invD G O w))) (powGS G O w (zG w) (uS G O w))
/-- `KeyGen`'s answer: `1 ‖ d_0 ‖ d_1`, or `⊥`. -/
private def ans1 (w : List Bool) : List Bool :=
  if keyOk w then true :: (d0S G O w ++ d1S G O w)
  else List.replicate ((aLen G ℓ 1).eval (rU w).length) false

/-- The first message `M_0` of a challenge query. -/
private def m0 (w : List Bool) : List Bool :=
  (rX w).take ((bb1Scheme G ℓ).msgLen.eval (rU w).length)
/-- The second message `M_1` of a challenge query. -/
private def m1 (w : List Bool) : List Bool :=
  (rX w).drop ((bb1Scheme G ℓ).msgLen.eval (rU w).length)
/-- The message `M_b`. -/
private def mB (w : List Bool) : List Bool := if b then m1 G ℓ w else m0 G ℓ w
/-- Whether both messages encode elements of `G_T` (`memT`). -/
private def valid (w : List Bool) : Bool :=
  (O.memT (pairEncode (zD w) (m0 G ℓ w))).headD false &&
    (O.memT (pairEncode (zD w) (m1 G ℓ w))).headD false
/-- The challenge `M_b · T ‖ Z ‖ Z^{α_1}`. -/
private def ctS (w : List Bool) : List Bool :=
  O.mulT (pairEncode (zD w) (pairEncode (mB G ℓ b w) (zT w))) ++ zZ w ++ powGS G O w (zZ w) (kA w)
/-- `Challenge`'s answer: `⊥` before `Init`, the recorded challenge, a fresh one, or `⊥`. -/
private def ans2 (w : List Bool) : List Bool :=
  if !sCom w then List.replicate ((aLen G ℓ 2).eval (rU w).length) false
  else if sChal w then sC G ℓ w
  else if valid G ℓ O w then ctS G ℓ O b w
  else List.replicate ((aLen G ℓ 2).eval (rU w).length) false

/-- The query is to `Init`. -/
private def isI (w : List Bool) : Bool := decide (rI w = [])
/-- The query is to `KeyGen`. -/
private def isK (w : List Bool) : Bool := decide (rI w = [true])

/-- The answer to the query. -/
private def ansW (w : List Bool) : List Bool :=
  if isI w then ans0 G O w else if isK w then ans1 G ℓ O w else ans2 G ℓ O b w
/-- The new commitment `o_1`. -/
private def newO1 (w : List Bool) : List Bool :=
  if isI w then pairEncode (tSel w) (aSel G O w) else sO1 w
/-- The new challenge record `o_2`. -/
private def newO2 (w : List Bool) : List Bool :=
  if isI w || isK w then sO2 G ℓ w
  else if sCom w && !sChal w && valid G ℓ O w then true :: ctS G ℓ O b w else sO2 G ℓ w

/-- **One round of the handler**: the answer and the new state
`⟨1^{j+1}, ⟨o_1', o_2'⟩⟩`, padded. -/
private def runF (w : List Bool) : List Bool :=
  pairEncode (ansW G ℓ O b w) (EnsembleLemmas.padL ((stLen G ℓ q).eval (rU w).length)
    (pairEncode (true :: sJ w) (pairEncode (newO1 G O w) (newO2 G ℓ O b w))))

/-! ### Polynomial time -/

section Poly

private theorem poly_hS (H : ArithmeticFP) {t a : List Bool → List Bool} (ht : PolyTimeComputable t)
    (ha : PolyTimeComputable a) : PolyTimeComputable fun w => hS G O w (t w) (a w) :=
  poly_mulGS G O (poly_powGS G O poly_zX (poly_negS G O H ht)) (poly_powGS G O poly_zG ha)
private theorem poly_tSel : PolyTimeComputable tSel :=
  polyTimeComputable_ite poly_sCom poly_kT poly_rX
private theorem poly_aSel (H : ArithmeticFP) : PolyTimeComputable (aSel G O) :=
  polyTimeComputable_ite poly_sCom poly_kA (poly_uS G O H)
private theorem poly_ans0 (H : ArithmeticFP) : PolyTimeComputable (ans0 G O) :=
  (((poly_zD.append poly_zG).append poly_zX).append poly_zY).append
    (poly_hS G O H poly_tSel (poly_aSel G O H))

private theorem poly_keyOk : PolyTimeComputable fun w => [keyOk w] :=
  polyTimeComputable_and poly_sCom (polyTimeComputable_not
    ((polyTimeComputable_pairEq.comp' (poly_rX.pairEncode poly_kT)).congr fun w => by
      simp only [pairFstD_pairEncode, pairSndD_pairEncode]))
private theorem poly_diffS (H : ArithmeticFP) : PolyTimeComputable (diffS G O) :=
  poly_addS G O H (poly_modS G O H poly_rX) (poly_negS G O H poly_kT)
private theorem poly_invD (H : ArithmeticFP) : PolyTimeComputable (invD G O) :=
  poly_invS G O H (poly_diffS G O H)
private theorem poly_d0S (H : ArithmeticFP) : PolyTimeComputable (d0S G O) :=
  poly_mulGS G O (poly_powGS G O poly_zY
      (poly_mulS G O H (poly_negS G O H poly_kA) (poly_invD G O H)))
    (poly_powGS G O (poly_mulGS G O (poly_powGS G O poly_zX (poly_modS G O H poly_rX))
      (poly_hS G O H poly_kT poly_kA)) (poly_uS G O H))
private theorem poly_d1S (H : ArithmeticFP) : PolyTimeComputable (d1S G O) :=
  poly_mulGS G O (poly_powGS G O poly_zY (poly_negS G O H (poly_invD G O H)))
    (poly_powGS G O poly_zG (poly_uS G O H))
private theorem poly_ans1 (H : ArithmeticFP) : PolyTimeComputable (ans1 G ℓ O) :=
  polyTimeComputable_ite poly_keyOk
    (((polyTimeComputable_const [true]).append ((poly_d0S G O H).append (poly_d1S G O H))).congr
      fun _ => List.singleton_append)
    (EnsembleLemmas.polyTimeComputable_zeros (aLen G ℓ 1) poly_rU)

private theorem poly_m0 : PolyTimeComputable (m0 G ℓ) :=
  ((polyTimeComputable_pairTakePoly (bb1Scheme G ℓ).msgLen).comp'
    (poly_rU.pairEncode poly_rX)).congr fun w => by
      simp only [pairFstD_pairEncode, pairSndD_pairEncode]; rfl
private theorem poly_m1 : PolyTimeComputable (m1 G ℓ) :=
  ((polyTimeComputable_pairDropPoly (bb1Scheme G ℓ).msgLen).comp'
    (poly_rU.pairEncode poly_rX)).congr fun w => by
      simp only [pairFstD_pairEncode, pairSndD_pairEncode]; rfl
private theorem poly_mB : PolyTimeComputable (mB G ℓ b) :=
  polyTimeComputable_ite (polyTimeComputable_const [b]) (poly_m1 G ℓ) (poly_m0 G ℓ)
private theorem poly_valid : PolyTimeComputable fun w => [valid G ℓ O w] :=
  polyTimeComputable_and
    (polyTimeComputable_headD.comp' (O.memT_poly.comp' (poly_zD.pairEncode (poly_m0 G ℓ))))
    (polyTimeComputable_headD.comp' (O.memT_poly.comp' (poly_zD.pairEncode (poly_m1 G ℓ))))
private theorem poly_ctS : PolyTimeComputable (ctS G ℓ O b) :=
  ((O.mulT_poly.comp' (poly_zD.pairEncode ((poly_mB G ℓ b).pairEncode poly_zT))).append
    poly_zZ).append (poly_powGS G O poly_zZ poly_kA)
private theorem poly_ans2 : PolyTimeComputable (ans2 G ℓ O b) :=
  polyTimeComputable_ite (polyTimeComputable_not poly_sCom)
    (EnsembleLemmas.polyTimeComputable_zeros (aLen G ℓ 2) poly_rU)
    (polyTimeComputable_ite poly_sChal (poly_sC G ℓ)
      (polyTimeComputable_ite (poly_valid G ℓ O) (poly_ctS G ℓ O b)
        (EnsembleLemmas.polyTimeComputable_zeros (aLen G ℓ 2) poly_rU)))

private theorem poly_isI : PolyTimeComputable fun w => [isI w] :=
  polyTimeComputable_isNil.comp' poly_rI
private theorem poly_isK : PolyTimeComputable fun w => [isK w] :=
  (polyTimeComputable_pairEq.comp' (poly_rI.pairEncode (polyTimeComputable_const [true]))).congr
    fun w => by simp only [pairFstD_pairEncode, pairSndD_pairEncode]; rfl
private theorem poly_ansW (H : ArithmeticFP) : PolyTimeComputable (ansW G ℓ O b) :=
  polyTimeComputable_ite poly_isI (poly_ans0 G O H)
    (polyTimeComputable_ite poly_isK (poly_ans1 G ℓ O H) (poly_ans2 G ℓ O b))
private theorem poly_newO1 (H : ArithmeticFP) : PolyTimeComputable (newO1 G O) :=
  polyTimeComputable_ite poly_isI (poly_tSel.pairEncode (poly_aSel G O H)) poly_sO1
private theorem poly_newO2 : PolyTimeComputable (newO2 G ℓ O b) :=
  polyTimeComputable_ite (polyTimeComputable_or poly_isI poly_isK) (poly_sO2 G ℓ)
    (polyTimeComputable_ite (polyTimeComputable_and (polyTimeComputable_and poly_sCom
        (polyTimeComputable_not poly_sChal)) (poly_valid G ℓ O))
      (((polyTimeComputable_const [true]).append (poly_ctS G ℓ O b)).congr
        fun _ => List.singleton_append)
      (poly_sO2 G ℓ))

/-- **One round of the handler is polynomial-time**: every field is a pair projection, a fixed
word, an operation of `O`, an arithmetic function of `H`, the drawn exponent (`poly_uS`), a test,
a branch or a padding (`EnsembleLemmas.polyTimeComputable_padL`). -/
private theorem poly_runF (H : ArithmeticFP) : PolyTimeComputable (runF G ℓ O b q) :=
  (poly_ansW G ℓ O b H).pairEncode (EnsembleLemmas.polyTimeComputable_padL (stLen G ℓ q) poly_rU
    ((((polyTimeComputable_const [true]).append poly_sJ).congr
        fun _ => List.singleton_append).pairEncode
      ((poly_newO1 G O H).pairEncode (poly_newO2 G ℓ O b))))

end Poly

/-! ### The handler -/

/-- **The handler of the reduction `B`** [BB04, proof of Theorem 4.1] for the challenge bit `b`
and the budget `q`: state `⟨1^j, ⟨o_1, o_2⟩⟩` padded to `2q + 4ℓ + 4wG + wT + 11` bits, initially
`⟨[], ⟨[], []⟩⟩`; seed `q(κ)` blocks of `n · n` bits; the adversary's input is empty; one round
answers one query (`runF`); the output is the adversary's. -/
def handler (H : ArithmeticFP) : PolyHandler 3 (qLen G ℓ) (aLen G ℓ) where
  stateLen := stLen G ℓ q
  seedLen := q.mul ((blockLen G).mul (blockLen G))
  init _ := padFin _ (pairEncode [] (pairEncode [] []))
  run := runF G ℓ O b q
  poly := poly_runF G ℓ O b q H
  advIn _ := []
  advIn_poly := polyTimeComputable_const []
  out w := pairSndD (pairSndD w)
  out_poly := polyTimeComputable_pairSndD.comp' polyTimeComputable_pairSndD

variable (H : ArithmeticFP)

/-- The handler's seed has `q(κ) · (n · n)` bits: `(handler …).seedLen = q · (n · n)`. -/
theorem handler_seedLen : (handler G ℓ O b q H).seedLen = q.mul ((blockLen G).mul (blockLen G)) :=
  rfl

/-- The adversary runs on the empty input: `(handler …).advInput κ z ω = []`. -/
theorem handler_advInput (κ : ℕ) (z : List Bool)
    (ω : Fin ((handler G ℓ O b q H).seedLen.eval κ) → Bool) :
    (handler G ℓ O b q H).advInput κ z ω = [] := by
  rw [PolyHandler.advInput_eq]
  rfl

/-- The reduction outputs the adversary's output: `(handler …).result κ z ω s a = ⟦a⟧`. -/
theorem handler_result (κ : ℕ) (z : List Bool)
    (ω : Fin ((handler G ℓ O b q H).seedLen.eval κ) → Bool)
    (s : Fin ((handler G ℓ O b q H).stateLen.eval κ) → Bool) {e : ℕ} (a : Fin e → Bool) :
    (handler G ℓ O b q H).result κ z ω s a = List.ofFn a := by
  rw [PolyHandler.result_eq]
  show pairSndD (pairSndD (pairEncode _ (pairEncode _ _))) = _
  rw [pairSndD_pairEncode, pairSndD_pairEncode]

/-- The seed length is `q(κ) · (n · n)`. -/
private theorem seedLen_eval (κ : ℕ) :
    (handler G ℓ O b q H).seedLen.eval κ =
      q.eval κ * ((blockLen G).eval κ * (blockLen G).eval κ) := by
  rw [handler_seedLen, PolyExpr.eval_mul, PolyExpr.eval_mul]

/-- **The seed as blocks**: `q(κ)` blocks of `n · n` bits, block `j` the `j`-th window of the
seed (`FunFamily.blocks`). -/
def seedBlocks (κ : ℕ) :
    (Fin ((handler G ℓ O b q H).seedLen.eval κ) → Bool) ≃
      (Fin (q.eval κ) → Fin ((blockLen G).eval κ * (blockLen G).eval κ) → Bool) :=
  (Equiv.arrowCongr (finCongr (seedLen_eval G ℓ O b q H κ)) (Equiv.refl Bool)).trans
    (FunFamily.blocks _ _)

/-- **Block `j` of the seed is its `j`-th window**:
`⟦seedBlocks … κ ω j⟧ = (⟦ω⟧.drop (j · n²)).take n²`. -/
theorem seedBlocks_window (κ : ℕ) (ω : Fin ((handler G ℓ O b q H).seedLen.eval κ) → Bool)
    (j : Fin (q.eval κ)) :
    List.ofFn (seedBlocks G ℓ O b q H κ ω j) =
      ((List.ofFn ω).drop (j * ((blockLen G).eval κ * (blockLen G).eval κ))).take
        ((blockLen G).eval κ * (blockLen G).eval κ) := by
  rw [seedBlocks, Equiv.trans_apply, FunFamily.ofFn_blocks, ofFn_arrowCongr_finCongr]

/-! ### The encoding of the simulator's states -/

/-- The commitment word: empty, or `⟨ID*, ⟦α_1⟧_{wG+1}⟩`. -/
private def o1Word (κ : ℕ) {d : List Bool} :
    Option ((Fin ((bb1Scheme G ℓ).idLen.eval κ) → Bool) × ZMod (G.group κ d).order) →
      List Bool
  | none => []
  | some (t, α₁) => pairEncode (List.ofFn t) (natToList ((aWidth G).eval κ) α₁.val)

/-- The challenge record: empty, or `1 ‖ C`. -/
private def o2Word (κ : ℕ) : Option (Fin ((bb1Scheme G ℓ).ctLen.eval κ) → Bool) → List Bool
  | none => []
  | some c => true :: List.ofFn c

/-- The state word `⟨1^j, ⟨o_1, o_2⟩⟩` of the simulator's state `s` after `j` queries. -/
private def stWord (κ : ℕ) {d : List Bool} (s : BB1SimState G ℓ κ d) (j : ℕ) : List Bool :=
  pairEncode (List.replicate j true) (pairEncode (o1Word G ℓ κ s.1) (o2Word G ℓ κ s.2))

/-- The handler's encoding of the simulator's state `s` after `j` queries: `stWord`, padded. -/
private def stEnc (κ : ℕ) {d : List Bool} (s : BB1SimState G ℓ κ d) (j : ℕ) :
    Fin ((handler G ℓ O b q H).stateLen.eval κ) → Bool :=
  padFin _ (stWord G ℓ κ s j)



/-! ### Reading an encoded state -/

/-- The length of `stLen`: `2q + 4ℓ + 4wG + wT + 11`. -/
private theorem stLen_eval (κ : ℕ) :
    (stLen G ℓ q).eval κ = 2 * q.eval κ + 4 * ℓ.eval κ + 4 * G.wG.eval κ + G.wT.eval κ + 11 := by
  simp only [stLen, PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const]
  ring

/-- `|o_1| ≤ 2ℓ + 2 + (wG + 1)`. -/
private theorem length_o1Word_le (κ : ℕ) {d : List Bool}
    (o : Option ((Fin ((bb1Scheme G ℓ).idLen.eval κ) → Bool) × ZMod (G.group κ d).order)) :
    (o1Word G ℓ κ o).length ≤ 2 * ℓ.eval κ + 2 + (G.wG.eval κ + 1) := by
  rcases o with _ | ⟨t, α₁⟩
  · simp only [o1Word, List.length_nil]
    omega
  · simp only [o1Word, length_pairEncode, List.length_ofFn, length_natToList, aWidth_eval]
    rw [bb1Scheme_idLen]

/-- `|o_2| ≤ 1 + (wT + 2 wG)`. -/
private theorem length_o2Word_le (κ : ℕ) (o : Option (Fin ((bb1Scheme G ℓ).ctLen.eval κ) → Bool)) :
    (o2Word G ℓ κ o).length ≤ 1 + (G.wT.eval κ + 2 * G.wG.eval κ) := by
  rcases o with _ | c
  · simp only [o2Word, List.length_nil]
    omega
  · simp only [o2Word, List.length_cons, List.length_ofFn]
    rw [bb1Scheme_ctLen, PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const]
    omega

/-- The state word fits in the state: `|⟨1^j, ⟨o_1, o_2⟩⟩| ≤ stLen` for `j ≤ q`. -/
private theorem length_stWord_le (κ : ℕ) {d : List Bool} (s : BB1SimState G ℓ κ d) (j : ℕ)
    (hj : j ≤ q.eval κ) : (stWord G ℓ κ s j).length ≤ (stLen G ℓ q).eval κ := by
  have h1 := length_o1Word_le G ℓ κ s.1
  have h2 := length_o2Word_le G ℓ κ s.2
  rw [stWord, length_pairEncode, length_pairEncode, List.length_replicate, stLen_eval]
  omega

/-- **The fields of an encoded state**: for `j ≤ q`, the encoded state of `s` reads as the counter
`1^j`, the commitment word `o_1` and the challenge record `o_2` followed by `false`s. -/
private theorem fields_stEnc (κ : ℕ) {d : List Bool} (s : BB1SimState G ℓ κ d) (j : ℕ)
    (hj : j ≤ q.eval κ) :
    ∃ k, List.ofFn (stEnc G ℓ O b q H κ s j) =
      pairEncode (List.replicate j true)
        (pairEncode (o1Word G ℓ κ s.1) (o2Word G ℓ κ s.2 ++ List.replicate k false)) := by
  show ∃ k, List.ofFn (padFin ((stLen G ℓ q).eval κ) (stWord G ℓ κ s j)) = _
  rw [Collection.ofFn_padFin_of_le (length_stWord_le G ℓ q κ s j hj), stWord,
    ← GGMRed.pairEncode_append_right, ← GGMRed.pairEncode_append_right]
  exact ⟨_, rfl⟩

/-- The padding of a challenge record: its first bit is the record's (`false` when empty). -/
private theorem headD_o2Word (κ : ℕ) (o : Option (Fin ((bb1Scheme G ℓ).ctLen.eval κ) → Bool))
    (k : ℕ) : (o2Word G ℓ κ o ++ List.replicate k false).headD false = o.isSome := by
  rcases o with _ | c
  · rcases k with _ | k <;> rfl
  · rfl

/-- The recorded challenge reads back from a padded record `1 ‖ C`. -/
private theorem take_o2Word (κ : ℕ) (c : Fin ((bb1Scheme G ℓ).ctLen.eval κ) → Bool) (k : ℕ) :
    ((o2Word G ℓ κ (some c) ++ List.replicate k false).drop 1).take
      ((bb1Scheme G ℓ).ctLen.eval κ) = List.ofFn c := by
  simp only [o2Word, List.cons_append, List.drop_succ_cons, List.drop_zero]
  exact List.take_left' List.length_ofFn

section State

variable {κ : ℕ} {w : List Bool} {d : List Bool} {s : BB1SimState G ℓ κ d} {j : ℕ}

/-- The counter, the commitment and the padded record of a round input with an encoded state. -/
private theorem fields_rS (hj : j ≤ q.eval κ) (hS : rS w = List.ofFn (stEnc G ℓ O b q H κ s j)) :
    ∃ k, sJ w = List.replicate j true ∧ sO1 w = o1Word G ℓ κ s.1 ∧
      sR w = o2Word G ℓ κ s.2 ++ List.replicate k false := by
  obtain ⟨k, hk⟩ := fields_stEnc G ℓ O b q H κ s j hj
  refine ⟨k, ?_, ?_, ?_⟩
  · rw [sJ_eq, hS, hk, pairFstD_pairEncode]
  · rw [sO1_eq, hS, hk, pairSndD_pairEncode, pairFstD_pairEncode]
  · rw [sR_eq, hS, hk, pairSndD_pairEncode, pairSndD_pairEncode]

end State



/-! ### One round on an encoded state -/

section Round

variable {κ : ℕ} {r : G.gen.Coins κ} {g X Y Z : (G.group κ (G.desc κ r)).G}
  {T : (G.group κ (G.desc κ r)).GT} {w : List Bool} {s : BB1SimState G ℓ κ (G.desc κ r)} {j : ℕ}


/-- **The encoded state after a round**: the new counter `1^{j+1}` and the new words `o_1`, `o_2`
of the state `s'`, padded, are the encoding of `s'` after `j + 1` queries. -/
private theorem padL_newState (hU : (rU w).length = κ) (hJ : sJ w = List.replicate j true)
    (s' : BB1SimState G ℓ κ (G.desc κ r)) {o1 o2 : List Bool} (h1 : o1 = o1Word G ℓ κ s'.1)
    (h2 : o2 = o2Word G ℓ κ s'.2) :
    EnsembleLemmas.padL ((stLen G ℓ q).eval (rU w).length)
        (pairEncode (true :: sJ w) (pairEncode o1 o2)) =
      List.ofFn (stEnc G ℓ O b q H κ s' (j + 1)) := by
  rw [hU, hJ, h1, h2, stEnc, EnsembleLemmas.ofFn_padFin_eq_padL, stWord, List.replicate_succ]
  rfl

/-- The commitment state of the round input: committed iff `s.1` is `some`. -/
private theorem sCom_of (hO1 : sO1 w = o1Word G ℓ κ s.1) : sCom w = s.1.isSome := by
  rw [sCom_eq, hO1]
  rcases s with ⟨_ | ⟨t, α₁⟩, c⟩
  · rfl
  · show (!decide (pairEncode _ _ = [])) = true
    rw [decide_eq_false (pairEncode_ne_nil _ _)]
    rfl

/-- The challenge record of the round input without its padding is `o_2`. -/
private theorem sO2_of (hU : (rU w).length = κ) {k : ℕ}
    (hR : sR w = o2Word G ℓ κ s.2 ++ List.replicate k false) :
    sO2 G ℓ w = o2Word G ℓ κ s.2 := by
  rw [sO2_eq, sChal_eq, hR, headD_o2Word]
  rcases s with ⟨o, _ | c⟩
  · rfl
  · show true :: sC G ℓ w = _
    rw [sC_eq, hR, hU, take_o2Word]
    rfl

/-- **The drawn exponent of the round**: the numeral `uS` is `⟦u.val⟧_{wG+1}` for the exponent
`u = draw (block j)` (`seedBlocks_window`, `uS_of_blkS`). -/
private theorem uS_of (hj : j < q.eval κ) (ω : Fin ((handler G ℓ O b q H).seedLen.eval κ) → Bool)
    (hU : (rU w).length = κ) (hD : zD w = G.desc κ r) (hW : rW w = List.ofFn ω)
    (hJ : sJ w = List.replicate j true) :
    uS G O w = natToList ((aWidth G).eval κ)
      (draw G κ (G.desc κ r) (seedBlocks G ℓ O b q H κ ω ⟨j, hj⟩)).val := by
  refine uS_of_blkS G O hU hD _ ?_
  rw [blkS_eq, hW, hJ, hU, List.length_replicate, seedBlocks_window, nn_eval]

/-- `h = X^{(−t).val} · g^{α}` on encodings, for the identity word `⟦t⟧` and `α`'s numeral. -/
private theorem hS_ofFn (hZ : rZ w = tupleStr (G.group κ (G.desc κ r)) (G.desc κ r) g X Y Z T)
    (tw : List Bool) (α₁ : ZMod (G.group κ (G.desc κ r)).order) :
    hS G O w tw (natToList ((aWidth G).eval κ) α₁.val) =
      List.ofFn ((G.group κ (G.desc κ r)).encG
        (X ^ (-((listToNat tw : ℕ) : ZMod (G.group κ (G.desc κ r)).order)).val * g ^ α₁.val)) := by
  have hD := zD_of hZ
  rw [hS, zX_of hZ, zG_of hZ, powGS_ofFn G O hD, powGS_ofFn G O hD, mulGS_ofFn G O hD,
    listToNat_negS G O (listToNat_pS G O hD), listToNat_natToList_val]


/-- The length of the parameters' word `d ‖ g ‖ X ‖ Y ‖ h` is `ppLen`. -/
private theorem length_ppWord (h : (G.group κ (G.desc κ r)).G) :
    (G.desc κ r ++ List.ofFn ((G.group κ (G.desc κ r)).encG g) ++
      List.ofFn ((G.group κ (G.desc κ r)).encG X) ++ List.ofFn ((G.group κ (G.desc κ r)).encG Y) ++
      List.ofFn ((G.group κ (G.desc κ r)).encG h)).length = (aLen G ℓ 0).eval κ := by
  simp only [List.length_append, List.length_ofFn, G.length_desc]
  rw [aLen_zero, bb1Scheme_ppLen, PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const]
  ring

/-- **The `Init` round**: on the encoding of `s` after `j < q` queries, the handler answers and
updates the state as `drawStep` does with the exponent `u` drawn from block `j`.

**Proof sketch.** Read the round input's fields (`rU_input`, `rZ_input`, `fields_rS`), take the
`Init` branch of `runF`, and split on the commitment of `s` (`sCom_of`). Before a commitment the
committed pair is the query and the drawn exponent (`uS_of`); after one, the recorded pair
(`kT_eq`, `kA_eq`). In both cases `h = X^{(−t).val} · g^{α_1.val}` on encodings (`hS_ofFn`), the
answer `d ‖ g ‖ X ‖ Y ‖ h` has `ppLen` bits (`length_ppWord`), the identity reads as its
numeral's residue (`idToZ_padFin`, `BB1.idToZ_eq`), and the new state is the encoding of the
state of `drawStep_zero` after `j + 1` queries (`padL_newState`). -/
private theorem runF_zero (hj : j < q.eval κ)
    (ω : Fin ((handler G ℓ O b q H).seedLen.eval κ) → Bool) (x : Fin ((qLen G ℓ 0).eval κ) → Bool)
    (s : BB1SimState G ℓ κ (G.desc κ r)) (y : Fin ((aLen G ℓ 0).eval κ) → Bool)
    (s' : BB1SimState G ℓ κ (G.desc κ r))
    (h : drawStep G ℓ b κ (G.desc κ r) g X Y Z T 0 x s
      (draw G κ (G.desc κ r) (seedBlocks G ℓ O b q H κ ω ⟨j, hj⟩)) = .pure (y, s')) :
    runF G ℓ O b q (PolyHandler.input κ (tupleStr (G.group κ (G.desc κ r)) (G.desc κ r) g X Y Z T)
        (List.ofFn ω) (List.ofFn (stEnc G ℓ O b q H κ s j)) (0 : Fin 3) (List.ofFn x)) =
      pairEncode (List.ofFn y) (List.ofFn (stEnc G ℓ O b q H κ s' (j + 1))) := by
  rw [drawStep_zero] at h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (OracleComp.pure.inj h)
  have hU : (rU (PolyHandler.input κ (tupleStr (G.group κ (G.desc κ r)) (G.desc κ r) g X Y Z T)
      (List.ofFn ω) (List.ofFn (stEnc G ℓ O b q H κ s j)) (0 : Fin 3)
        (List.ofFn x))).length = κ := by
    rw [rU_input, List.length_replicate]
  have hZ := rZ_input (κ := κ) (z := tupleStr (G.group κ (G.desc κ r)) (G.desc κ r) g X Y Z T)
    (W := List.ofFn ω) (S := List.ofFn (stEnc G ℓ O b q H κ s j)) (i := 0) (X := List.ofFn x)
  have hD := zD_of hZ
  obtain ⟨k, hJ, hO1, hR⟩ := fields_rS G ℓ O b q H hj.le rS_input
  have hlen : (qLen G ℓ 0).eval κ = (bb1Scheme G ℓ).idLen.eval κ := by rw [qLen_zero]
  rw [runF, ansW, newO1, newO2, show isI _ = true by rw [isI, rI_input]; rfl, if_pos rfl,
    if_pos rfl, Bool.true_or, if_pos rfl, ans0, zD_of hZ, zG_of hZ, zX_of hZ, zY_of hZ,
    sO2_of G ℓ hU hR]
  rcases s with ⟨_ | ⟨t, α₁⟩, c⟩
  · -- before a commitment: the query and the drawn exponent
    have hcom : sCom (PolyHandler.input κ (tupleStr (G.group κ (G.desc κ r)) (G.desc κ r) g X Y Z T)
        (List.ofFn ω) (List.ofFn (stEnc G ℓ O b q H κ (none, c) j)) (0 : Fin 3)
          (List.ofFn x)) = false :=
      sCom_of G ℓ hO1
    rw [tSel, aSel, hcom, if_neg Bool.false_ne_true, if_neg Bool.false_ne_true, rX_input,
      uS_of G ℓ O b q H hj ω hU hD rW_input hJ, hS_ofFn G O hZ]
    simp only [Option.getD_none]
    congr 1
    · rw [ofFn_padFin_of_length (length_ppWord G ℓ _), idToZ_padFin G ℓ x hlen]
    · refine padL_newState G ℓ O b q H hU hJ _ ?_ rfl
      simp only [o1Word]
      rw [ofFn_padFin_of_length (by rw [List.length_ofFn, hlen])]
  · -- after a commitment: the recorded identity and exponent
    have hcom : sCom (PolyHandler.input κ (tupleStr (G.group κ (G.desc κ r)) (G.desc κ r) g X Y Z T)
        (List.ofFn ω) (List.ofFn (stEnc G ℓ O b q H κ (some (t, α₁), c) j)) (0 : Fin 3)
        (List.ofFn x)) =
        true := sCom_of G ℓ hO1
    rw [tSel, aSel, hcom, if_pos rfl, if_pos rfl, kT_eq, kA_eq, hO1]
    simp only [o1Word, pairFstD_pairEncode, pairSndD_pairEncode, Option.getD_some]
    rw [hS_ofFn G O hZ]
    congr 1
    · rw [ofFn_padFin_of_length (length_ppWord G ℓ _), BB1.idToZ_eq,
        NumberTheory.bitsToNat_eq_listToNat]
    · exact padL_newState G ℓ O b q H hU hJ _ rfl rfl


/-- **The key of `KeyGen` on encodings, first component**: with the query `⟦x⟧`, the committed
identity `⟦t⟧`, `α_1`'s numeral and the drawn `u`'s numeral, `d0S` is the encoding of
`Y^{(−α_1/(x − t)).val} · (X^{x.val} · (X^{(−t).val} g^{α_1.val}))^{u.val}`, identities read as
their numerals' residues.

**Proof sketch.** Unfold `d0S` (this file) and rewrite each field and operation by its value on
encodings: the tuple's fields (`zX_of`, `zY_of`), the group operations (`powGS_ofFn`,
`mulGS_ofFn`, `hS_ofFn`) and the residue arithmetic (`listToNat_modS`, …, `listToNat_invS`),
then `ZMod.natCast_zmod_val`, `div_eq_mul_inv` and `sub_eq_add_neg` align the exponents. -/
private theorem d0S_of (hZ : rZ w = tupleStr (G.group κ (G.desc κ r)) (G.desc κ r) g X Y Z T)
    (xw tw : List Bool) (α₁ u : ZMod (G.group κ (G.desc κ r)).order) (hX : rX w = xw)
    (hT : kT w = tw) (hA : kA w = natToList ((aWidth G).eval κ) α₁.val)
    (hu : uS G O w = natToList ((aWidth G).eval κ) u.val) :
    d0S G O w = List.ofFn ((G.group κ (G.desc κ r)).encG
      (Y ^ (-α₁ / ((listToNat xw : ℕ) - (listToNat tw : ℕ) :
          ZMod (G.group κ (G.desc κ r)).order)).val *
        (X ^ ((listToNat xw : ℕ) : ZMod (G.group κ (G.desc κ r)).order).val *
          (X ^ (-((listToNat tw : ℕ) : ZMod (G.group κ (G.desc κ r)).order)).val * g ^ α₁.val)) ^
          u.val)) := by
  have hD := zD_of hZ
  have hp := listToNat_pS G O hD
  simp only [d0S, hT, hA, hu, hX, hS_ofFn G O hZ, zX_of hZ, zY_of hZ, powGS_ofFn G O hD,
    mulGS_ofFn G O hD, listToNat_natToList_val, listToNat_modS G O hp, listToNat_mulS G O hp,
    invD, listToNat_negS G O hp, listToNat_invS G O hp, diffS, listToNat_addS G O hp,
    ZMod.natCast_zmod_val, div_eq_mul_inv, sub_eq_add_neg]

/-- **The key of `KeyGen` on encodings, second component**: `d1S` is the encoding of
`Y^{(−1/(x − t)).val} · g^{u.val}`. -/
private theorem d1S_of (hZ : rZ w = tupleStr (G.group κ (G.desc κ r)) (G.desc κ r) g X Y Z T)
    (xw tw : List Bool) (u : ZMod (G.group κ (G.desc κ r)).order) (hX : rX w = xw)
    (hT : kT w = tw) (hu : uS G O w = natToList ((aWidth G).eval κ) u.val) :
    d1S G O w = List.ofFn ((G.group κ (G.desc κ r)).encG
      (Y ^ (-1 / ((listToNat xw : ℕ) - (listToNat tw : ℕ) :
          ZMod (G.group κ (G.desc κ r)).order)).val * g ^ u.val)) := by
  have hD := zD_of hZ
  have hp := listToNat_pS G O hD
  simp only [d1S, hu, hX, hT, zY_of hZ, zG_of hZ, powGS_ofFn G O hD, mulGS_ofFn G O hD,
    listToNat_natToList_val, listToNat_negS G O hp, invD, listToNat_invS G O hp, diffS,
    listToNat_addS G O hp, listToNat_modS G O hp, ZMod.natCast_zmod_val, neg_div, one_div,
    sub_eq_add_neg]

/-- **The `KeyGen` round**: on the encoding of `s` after `j < q` queries, the handler answers and
updates the state as `drawStep` does with the exponent `u` drawn from block `j`.

**Proof sketch.** Read the fields as for `Init` and take the `KeyGen` branch of `runF`, which
keeps `o_1` and `o_2`. Before `Init` the answer is `⊥` (`drawStep_one_none`). After it, split on
`⟦x⟧ = ⟦t⟧`: for the committed identity the answer is `⊥` (`drawStep_one_target`); otherwise it is
`1 ‖ d_0 ‖ d_1` with `r = u` drawn from block `j` (`drawStep_one_key`, `d0S_of`, `d1S_of`,
`uS_of`), of `1 + 2 wG` bits, with the identities read as their numerals' residues. The state is
re-encoded after `j + 1` queries (`padL_newState`). -/
private theorem runF_one (hj : j < q.eval κ)
    (ω : Fin ((handler G ℓ O b q H).seedLen.eval κ) → Bool) (x : Fin ((qLen G ℓ 1).eval κ) → Bool)
    (s : BB1SimState G ℓ κ (G.desc κ r)) (y : Fin ((aLen G ℓ 1).eval κ) → Bool)
    (s' : BB1SimState G ℓ κ (G.desc κ r))
    (h : drawStep G ℓ b κ (G.desc κ r) g X Y Z T 1 x s
      (draw G κ (G.desc κ r) (seedBlocks G ℓ O b q H κ ω ⟨j, hj⟩)) = .pure (y, s')) :
    runF G ℓ O b q (PolyHandler.input κ (tupleStr (G.group κ (G.desc κ r)) (G.desc κ r) g X Y Z T)
        (List.ofFn ω) (List.ofFn (stEnc G ℓ O b q H κ s j)) (1 : Fin 3) (List.ofFn x)) =
      pairEncode (List.ofFn y) (List.ofFn (stEnc G ℓ O b q H κ s' (j + 1))) := by
  have hU : (rU (PolyHandler.input κ (tupleStr (G.group κ (G.desc κ r)) (G.desc κ r) g X Y Z T)
      (List.ofFn ω) (List.ofFn (stEnc G ℓ O b q H κ s j)) (1 : Fin 3)
        (List.ofFn x))).length = κ := by
    rw [rU_input, List.length_replicate]
  have hZ := rZ_input (κ := κ) (z := tupleStr (G.group κ (G.desc κ r)) (G.desc κ r) g X Y Z T)
    (W := List.ofFn ω) (S := List.ofFn (stEnc G ℓ O b q H κ s j)) (i := 1) (X := List.ofFn x)
  have hD := zD_of hZ
  obtain ⟨k, hJ, hO1, hR⟩ := fields_rS G ℓ O b q H hj.le rS_input
  have hlen : (qLen G ℓ 1).eval κ = (bb1Scheme G ℓ).idLen.eval κ := by rw [qLen_one]
  have hlen1 : (aLen G ℓ 1).eval κ = 1 + 2 * G.wG.eval κ := by
    rw [aLen_one, PolyExpr.eval_add, PolyExpr.eval_const, bb1Scheme_skLen, PolyExpr.eval_mul,
      PolyExpr.eval_const]
    omega
  rw [runF, ansW, newO1, newO2, show isI _ = false by rw [isI, rI_input]; rfl,
    show isK _ = true by rw [isK, rI_input]; rfl, if_neg Bool.false_ne_true, if_pos rfl,
    if_neg Bool.false_ne_true, Bool.false_or, if_pos rfl, sO2_of G ℓ hU hR, ans1, keyOk]
  rcases s with ⟨_ | ⟨t, α₁⟩, c⟩
  · -- before `Init`: `⊥`
    rw [drawStep_one_none] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (OracleComp.pure.inj h)
    rw [sCom_of G ℓ hO1]
    simp only [Option.isSome_none, Bool.false_and, Bool.false_eq_true, if_false]
    congr 1
    · rw [hU, ofFn_zeroBits]
    · exact padL_newState G ℓ O b q H hU hJ _ hO1 rfl
  · have hcom := sCom_of G ℓ (s := (some (t, α₁), c)) hO1
    have hT : kT (PolyHandler.input κ (tupleStr (G.group κ (G.desc κ r)) (G.desc κ r) g X Y Z T)
        (List.ofFn ω) (List.ofFn (stEnc G ℓ O b q H κ (some (t, α₁), c) j)) (1 : Fin 3)
          (List.ofFn x)) = List.ofFn t := by
      rw [kT_eq, hO1]
      simp only [o1Word, pairFstD_pairEncode]
    have hA : kA (PolyHandler.input κ (tupleStr (G.group κ (G.desc κ r)) (G.desc κ r) g X Y Z T)
        (List.ofFn ω) (List.ofFn (stEnc G ℓ O b q H κ (some (t, α₁), c) j)) (1 : Fin 3)
          (List.ofFn x)) = natToList ((aWidth G).eval κ) α₁.val := by
      rw [kA_eq, hO1]
      simp only [o1Word, pairSndD_pairEncode]
    rw [hcom, rX_input, hT]
    simp only [Option.isSome_some, Bool.true_and]
    by_cases hx : List.ofFn x = List.ofFn t
    · -- the committed identity: `⊥`
      rw [drawStep_one_target G ℓ b κ _ g X Y Z T x t α₁ c _ hx] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (OracleComp.pure.inj h)
      rw [decide_eq_true hx, Bool.not_true, if_neg Bool.false_ne_true]
      congr 1
      · rw [hU, ofFn_zeroBits]
      · exact padL_newState G ℓ O b q H hU hJ _ hO1 rfl
    · -- another identity: the simulated key with `r = u`
      rw [drawStep_one_key G ℓ b κ _ g X Y Z T x t α₁ c _ hx] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (OracleComp.pure.inj h)
      rw [decide_eq_false hx, Bool.not_false, if_pos rfl,
        d0S_of G O hZ (List.ofFn x) (List.ofFn t) α₁ _ rX_input hT hA
          (uS_of G ℓ O b q H hj ω hU hD rW_input hJ),
        d1S_of G O hZ (List.ofFn x) (List.ofFn t) _ rX_input hT
          (uS_of G ℓ O b q H hj ω hU hD rW_input hJ)]
      congr 1
      · rw [ofFn_padFin_of_length (by
            simp only [List.length_cons, List.length_append, List.length_ofFn]
            rw [hlen1]; omega),
          idToZ_padFin G ℓ x hlen, BB1.idToZ_eq, NumberTheory.bitsToNat_eq_listToNat]
      · exact padL_newState G ℓ O b q H hU hJ _ hO1 rfl



/-- The ciphertext word `M · T ‖ Z ‖ Z^{α_1}` has `ctLen` bits. -/
private theorem length_ctWord (m : (G.group κ (G.desc κ r)).GT)
    (α₁ : ZMod (G.group κ (G.desc κ r)).order) :
    (List.ofFn ((G.group κ (G.desc κ r)).encT m) ++ List.ofFn ((G.group κ (G.desc κ r)).encG Z) ++
      List.ofFn ((G.group κ (G.desc κ r)).encG (Z ^ α₁.val))).length =
      (bb1Scheme G ℓ).ctLen.eval κ := by
  simp only [List.length_append, List.length_ofFn]
  rw [bb1Scheme_ctLen, PolyExpr.eval_add, PolyExpr.eval_mul, PolyExpr.eval_const]
  ring

/-- **The `Challenge` round**: on the encoding of `s` after `j < q` queries, the handler answers
and updates the state as `drawStep` does.

**Proof sketch.** Read the fields as for `Init` and take the `Challenge` branch of `runF`. Before
`Init` the answer is `⊥` (`drawStep_two_none`). After it, split on the recorded challenge
(`sChal_eq`, `headD_o2Word`): a recorded `C` is repeated (`drawStep_two_repeat`, `take_o2Word`).
Otherwise the handler's test `valid` is the test of `drawStep` that both halves of the query
(`take`/`drop` of `msgLen` bits) encode elements of `G_T` (`memT_headD`); if it holds, the selected
half is some `encT v`, and the answer `M_b · T ‖ Z ‖ Z^{α_1}` (`mulT_ofFn`, `powGS_ofFn`, of
`ctLen` bits by `length_ctWord`) is recorded as `o_2` (`drawStep_two_fresh`); if not, the answer is
`⊥` (`drawStep_two_invalid`). The state is re-encoded after `j + 1` queries
(`padL_newState`). -/
private theorem runF_two (hj : j < q.eval κ)
    (ω : Fin ((handler G ℓ O b q H).seedLen.eval κ) → Bool) (x : Fin ((qLen G ℓ 2).eval κ) → Bool)
    (s : BB1SimState G ℓ κ (G.desc κ r)) (y : Fin ((aLen G ℓ 2).eval κ) → Bool)
    (s' : BB1SimState G ℓ κ (G.desc κ r)) (u : ZMod (G.group κ (G.desc κ r)).order)
    (h : drawStep G ℓ b κ (G.desc κ r) g X Y Z T 2 x s u = .pure (y, s')) :
    runF G ℓ O b q (PolyHandler.input κ (tupleStr (G.group κ (G.desc κ r)) (G.desc κ r) g X Y Z T)
        (List.ofFn ω) (List.ofFn (stEnc G ℓ O b q H κ s j)) (2 : Fin 3) (List.ofFn x)) =
      pairEncode (List.ofFn y) (List.ofFn (stEnc G ℓ O b q H κ s' (j + 1))) := by
  classical
  have hU : (rU (PolyHandler.input κ (tupleStr (G.group κ (G.desc κ r)) (G.desc κ r) g X Y Z T)
      (List.ofFn ω) (List.ofFn (stEnc G ℓ O b q H κ s j)) (2 : Fin 3)
        (List.ofFn x))).length = κ := by
    rw [rU_input, List.length_replicate]
  have hZ := rZ_input (κ := κ) (z := tupleStr (G.group κ (G.desc κ r)) (G.desc κ r) g X Y Z T)
    (W := List.ofFn ω) (S := List.ofFn (stEnc G ℓ O b q H κ s j)) (i := 2) (X := List.ofFn x)
  have hD := zD_of hZ
  obtain ⟨k, hJ, hO1, hR⟩ := fields_rS G ℓ O b q H hj.le rS_input
  have hmsg : (bb1Scheme G ℓ).msgLen.eval κ = G.wT.eval κ := by rw [bb1Scheme_msgLen]
  have hx2 : (List.ofFn x).length = (bb1Scheme G ℓ).msgLen.eval κ +
      (bb1Scheme G ℓ).msgLen.eval κ := by
    rw [List.length_ofFn, qLen_two, PolyExpr.eval_add]
  have hct : (aLen G ℓ 2).eval κ = (bb1Scheme G ℓ).ctLen.eval κ := by rw [aLen_two]
  rw [runF, ansW, newO1, newO2, show isI _ = false by rw [isI, rI_input]; rfl,
    show isK _ = false by rw [isK, rI_input]; rfl, if_neg Bool.false_ne_true,
    if_neg Bool.false_ne_true, if_neg Bool.false_ne_true, Bool.false_or, if_neg Bool.false_ne_true,
    sO2_of G ℓ hU hR, ans2, sCom_of G ℓ hO1]
  rcases s with ⟨_ | ⟨t, α₁⟩, c⟩
  · -- before `Init`: `⊥`
    rw [drawStep_two_none] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (OracleComp.pure.inj h)
    simp only [Option.isSome_none, Bool.not_false, Bool.false_and, Bool.false_eq_true, if_false,
      if_true]
    congr 1
    · rw [hU, ofFn_zeroBits]
    · exact padL_newState G ℓ O b q H hU hJ _ hO1 rfl
  · have hchal : sChal (PolyHandler.input κ
        (tupleStr (G.group κ (G.desc κ r)) (G.desc κ r) g X Y Z T) (List.ofFn ω)
        (List.ofFn (stEnc G ℓ O b q H κ (some (t, α₁), c) j)) (2 : Fin 3)
          (List.ofFn x)) = c.isSome := by
      rw [sChal_eq, hR, headD_o2Word]
    simp only [Option.isSome_some, Bool.not_true, Bool.false_eq_true, if_false, Bool.true_and,
      hchal]
    rcases c with _ | c
    · -- no challenge yet
      have hA : kA (PolyHandler.input κ (tupleStr (G.group κ (G.desc κ r)) (G.desc κ r) g X Y Z T)
          (List.ofFn ω) (List.ofFn (stEnc G ℓ O b q H κ (some (t, α₁), none) j)) (2 : Fin 3)
            (List.ofFn x)) = natToList ((aWidth G).eval κ) α₁.val := by
        rw [kA_eq, hO1]
        simp only [o1Word, pairSndD_pairEncode]
      have hl0 : ((List.ofFn x).take ((bb1Scheme G ℓ).msgLen.eval κ)).length = G.wT.eval κ := by
        rw [List.length_take, hx2, ← hmsg]
        omega
      have hl1 : ((List.ofFn x).drop ((bb1Scheme G ℓ).msgLen.eval κ)).length = G.wT.eval κ := by
        rw [List.length_drop, hx2, ← hmsg]
        omega
      have hvalid : valid G ℓ O (PolyHandler.input κ
          (tupleStr (G.group κ (G.desc κ r)) (G.desc κ r) g X Y Z T) (List.ofFn ω)
          (List.ofFn (stEnc G ℓ O b q H κ (some (t, α₁), none) j)) (2 : Fin 3) (List.ofFn x)) =
          decide ((∃ v, List.ofFn ((G.group κ (G.desc κ r)).encT v) =
              (List.ofFn x).take ((bb1Scheme G ℓ).msgLen.eval κ)) ∧
            (∃ v, List.ofFn ((G.group κ (G.desc κ r)).encT v) =
              (List.ofFn x).drop ((bb1Scheme G ℓ).msgLen.eval κ))) := by
        rw [valid, m0, m1, rX_input, hU, memT_headD G O hD _ hl0, memT_headD G O hD _ hl1,
          Bool.decide_and]
      simp only [Option.isSome_none, Bool.not_false, Bool.true_and, Bool.false_eq_true,
        if_false]
      rw [hvalid]
      by_cases hc : (∃ v, List.ofFn ((G.group κ (G.desc κ r)).encT v) =
            (List.ofFn x).take ((bb1Scheme G ℓ).msgLen.eval κ)) ∧
          (∃ v, List.ofFn ((G.group κ (G.desc κ r)).encT v) =
            (List.ofFn x).drop ((bb1Scheme G ℓ).msgLen.eval κ))
      · -- a fresh valid challenge: `M_b · T ‖ Z ‖ Z^{α_1}`, recorded
        rw [drawStep_two_fresh G ℓ b κ _ g X Y Z T x t α₁ u hc] at h
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (OracleComp.pure.inj h)
        rw [decide_eq_true hc, if_pos rfl, if_pos rfl]
        -- the selected message is an encoding `encT v`
        obtain ⟨v, hv⟩ : ∃ v, List.ofFn ((G.group κ (G.desc κ r)).encT v) =
            (if b then (List.ofFn x).drop ((bb1Scheme G ℓ).msgLen.eval κ)
              else (List.ofFn x).take ((bb1Scheme G ℓ).msgLen.eval κ)) := by
          cases b
          · exact hc.1
          · exact hc.2
        have hmB : mB G ℓ b (PolyHandler.input κ
            (tupleStr (G.group κ (G.desc κ r)) (G.desc κ r) g X Y Z T) (List.ofFn ω)
            (List.ofFn (stEnc G ℓ O b q H κ (some (t, α₁), none) j)) (2 : Fin 3) (List.ofFn x)) =
            List.ofFn ((G.group κ (G.desc κ r)).encT v) := by
          rw [hv, mB, m0, m1, rX_input, hU]
        have hct' : ctS G ℓ O b (PolyHandler.input κ
            (tupleStr (G.group κ (G.desc κ r)) (G.desc κ r) g X Y Z T) (List.ofFn ω)
            (List.ofFn (stEnc G ℓ O b q H κ (some (t, α₁), none) j)) (2 : Fin 3) (List.ofFn x)) =
            List.ofFn ((G.group κ (G.desc κ r)).encT
              (BB1.decodeT (G.group κ (G.desc κ r)) (padFin _
                (if b then (List.ofFn x).drop ((bb1Scheme G ℓ).msgLen.eval κ)
                  else (List.ofFn x).take ((bb1Scheme G ℓ).msgLen.eval κ))) * T)) ++
              List.ofFn ((G.group κ (G.desc κ r)).encG Z) ++
              List.ofFn ((G.group κ (G.desc κ r)).encG (Z ^ α₁.val)) := by
          rw [ctS, hmB, zT_of hZ, mulT_ofFn G O hD, zZ_of hZ, hA, powGS_ofFn G O hD,
            listToNat_natToList_val, ← hv, padFin_ofFn, BB1.decodeT_encT]
        rw [hct']
        congr 1
        · rw [ofFn_padFin_of_length (by rw [length_ctWord G ℓ, hct])]
        · refine padL_newState G ℓ O b q H hU hJ _ hO1 ?_
          simp only [o2Word]
          rw [ofFn_padFin_of_length (length_ctWord G ℓ _ _)]
      · -- a message outside `G_T`: `⊥`
        rw [drawStep_two_invalid G ℓ b κ _ g X Y Z T x t α₁ u hc] at h
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj (OracleComp.pure.inj h)
        rw [decide_eq_false hc]
        simp only [Bool.false_eq_true, if_false]
        congr 1
        · rw [hU, ofFn_zeroBits]
        · exact padL_newState G ℓ O b q H hU hJ _ hO1 rfl
    · -- a recorded challenge: repeated
      rw [drawStep_two_repeat] at h
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj (OracleComp.pure.inj h)
      simp only [Option.isSome_some, Bool.not_true, Bool.false_and, if_true, Bool.false_eq_true,
        if_false]
      congr 1
      · rw [sC_eq, hR, hU, take_o2Word,
          ofFn_padFin_of_length (by rw [List.length_ofFn, hct])]
      · exact padL_newState G ℓ O b q H hU hJ _ hO1 rfl


end Round


/-! ### The handler's run -/

/-- **One query to the handler on an encoded state is one query to `drawStep`**: from the
encoding of `s` after `j < q` queries, the handler answers like `drawStep` with the exponent of
the tape `V j = draw (block j)`, and moves to the encoding of the new state after `j + 1`
queries.

**Proof sketch.** The tape's `j`-th entry is the draw from block `j` (`AdaptiveCPA.extTape_of_lt`),
and `drawStep` answers with some `(y, s')` (`exists_drawStep_eq_pure`), which is the tape run's
step (`ETTGame.tapeImpl_apply`). The handler's call answers with the first component of `runF` on
the round input (`PolyHandler.impl_apply`, `PolyHandler.answer_of_run_eq`), which the round
lemmas `runF_zero`, `runF_one`, `runF_two` identify with `y` and the encoding of `s'`. -/
private theorem handler_impl_stEnc (κ : ℕ) (r : G.gen.Coins κ)
    (g X Y Z : (G.group κ (G.desc κ r)).G) (T : (G.group κ (G.desc κ r)).GT)
    (ω : Fin ((handler G ℓ O b q H).seedLen.eval κ) → Bool) (i : Fin 3)
    (x : Fin ((qLen G ℓ i).eval κ) → Bool)
    (st : BB1SimState G ℓ κ (G.desc κ r) × ℕ) (hj : st.2 < q.eval κ) :
    ∃ (y : Fin ((aLen G ℓ i).eval κ) → Bool) (st' : BB1SimState G ℓ κ (G.desc κ r) × ℕ),
      ETTGame.tapeImpl (spec := bitSpecAt (qLen G ℓ) (aLen G ℓ) κ)
          (drawStep G ℓ b κ (G.desc κ r) g X Y Z T)
          (AdaptiveCPA.extTape fun j => draw G κ (G.desc κ r) (seedBlocks G ℓ O b q H κ ω j))
          i x st = .pure (y, st') ∧ st'.2 ≤ st.2 + 1 ∧
        (handler G ℓ O b q H).impl κ (tupleStr (G.group κ (G.desc κ r)) (G.desc κ r) g X Y Z T) ω i
          x (stEnc G ℓ O b q H κ st.1 st.2) = .pure (y, stEnc G ℓ O b q H κ st'.1 st'.2) := by
  obtain ⟨s, j⟩ := st
  have hV : AdaptiveCPA.extTape (fun j => draw G κ (G.desc κ r) (seedBlocks G ℓ O b q H κ ω j)) j =
      draw G κ (G.desc κ r) (seedBlocks G ℓ O b q H κ ω ⟨j, hj⟩) :=
    AdaptiveCPA.extTape_of_lt _ hj
  obtain ⟨y, s', hds⟩ := exists_drawStep_eq_pure G ℓ b κ (G.desc κ r) g X Y Z T i x s
    (draw G κ (G.desc κ r) (seedBlocks G ℓ O b q H κ ω ⟨j, hj⟩))
  refine ⟨y, (s', j + 1), ?_, le_rfl, ?_⟩
  · rw [ETTGame.tapeImpl_apply, hV, hds, OracleComp.pure_bind]
  · rw [PolyHandler.impl_apply]
    refine congrArg OracleComp.pure (PolyHandler.answer_of_run_eq _ ?_)
    show runF G ℓ O b q _ = _
    match i, x, y, hds with
    | 0, x, y, hds => exact runF_zero G ℓ O b q H hj ω x s y s' hds
    | 1, x, y, hds => exact runF_one G ℓ O b q H hj ω x s y s' hds
    | 2, x, y, hds => exact runF_two G ℓ O b q H hj ω x s y s' _ hds

/-- **The handler's run is the run of `drawStep` with exponents from the seed** [BB04, proof of
Theorem 4.1, the algorithm `B`]: for a computation `c` with at most `q(κ)` queries, simulating
`c` against the handler on the Decision BDH string of `(g, X, Y, Z, T)` and the seed `ω`, from its
initial state, is simulating `c` against `drawStep` with the exponent of the `j`-th query read
from the tape `V j = draw (block j of ω)` (`ETTGame.tapeImpl`), from the empty state, with the
final state read through an encoding `f`.

**Proof sketch.** `Games.simulate_eq_of_abs_bounded` with the counter of queries and the encoding
of the simulator's states: from the encoding of a state after `j < q(κ)` queries, the handler and
`drawStep` give the same answer and corresponding states (`handler_impl_stEnc`: the round
function `runF` reads the counter, the commitment and the challenge record from the padded state,
draws the exponent from block `j` of the seed, and computes the answer of `Init`, `KeyGen` or
`Challenge` with the operations of `O` and the arithmetic of `H`, `runF_zero`, `runF_one`,
`runF_two`); the initial state is the encoding of the empty state. -/
theorem simulate_handler (κ : ℕ) (r : G.gen.Coins κ) (g X Y Z : (G.group κ (G.desc κ r)).G)
    (T : (G.group κ (G.desc κ r)).GT) (ω : Fin ((handler G ℓ O b q H).seedLen.eval κ) → Bool)
    {α : Type} (c : OracleComp (bitSpecAt (qLen G ℓ) (aLen G ℓ) κ) α)
    (hc : c.CostBoundedBy (fun _ => 1) (q.eval κ)) :
    ∃ f : BB1SimState G ℓ κ (G.desc κ r) × ℕ → (Fin ((handler G ℓ O b q H).stateLen.eval κ) → Bool),
      simulate ((handler G ℓ O b q H).impl κ
          (tupleStr (G.group κ (G.desc κ r)) (G.desc κ r) g X Y Z T) ω) c
          ((handler G ℓ O b q H).init κ) =
        (simulate (ETTGame.tapeImpl (spec := bitSpecAt (qLen G ℓ) (aLen G ℓ) κ)
          (drawStep G ℓ b κ (G.desc κ r) g X Y Z T)
          (AdaptiveCPA.extTape fun j => draw G κ (G.desc κ r) (seedBlocks G ℓ O b q H κ ω j)))
          c ((none, none), 0)).bind fun p => .pure (p.1, f p.2) := by
  refine ⟨fun st => stEnc G ℓ O b q H κ st.1 st.2, ?_⟩
  have hinit : (handler G ℓ O b q H).init κ =
      stEnc G ℓ O b q H κ (d := G.desc κ r) (none, none) 0 := rfl
  rw [hinit]
  exact simulate_eq_of_abs_bounded _ _ (fun st => stEnc G ℓ O b q H κ st.1 st.2) Prod.snd
    (q.eval κ) (fun i x st hst => handler_impl_stEnc G ℓ O b q H κ r g X Y Z T ω i x st hst) c
    (q.eval κ) hc ((none, none), 0) (by omega)


end

end BB1Machine

end TCSlib.Cryptography.AdvancedEncryption.IdentityBased
